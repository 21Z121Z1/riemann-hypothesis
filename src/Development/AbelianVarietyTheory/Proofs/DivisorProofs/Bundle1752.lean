import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPairPartnerF

theorem pair_partnerF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartnerF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageInertiaOfPotentialGoodReductionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_inertia_of_potentialGoodReduction_alt : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → HasPotentialGoodReduction R K A → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  first | exact @GlobalTheory.finite_image_inertia_of_potentialGoodReduction | exact GlobalTheory.finite_image_inertia_of_potentialGoodReduction | (intros; apply GlobalTheory.finite_image_inertia_of_potentialGoodReduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem evAt_congr' {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt ξ h f = evAt ξ' h' f := by
  subst e; rfl

theorem top_le_preimage_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro z _
  exact h (Set.mem_univ (f z))

theorem finite_centre_not_mem (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E]
    [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) (hx : IsGenOver k x) (V : C.Opens) (hV : (V : Set C).Nonempty) :
    {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  have hC := hx.1
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  obtain ⟨z, hz⟩ := hV
  obtain ⟨V', hV'a, hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens hz
  have hV'a : IsAffineOpen V' := hV'a
  obtain ⟨hxV', -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨z, hzV'⟩
  obtain ⟨ev1, ev2, -, -, ev5, ev6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  let f : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hxV')
  haveI := hC.1
  haveI : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have eV : V' ≤ strHom k C ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let ψ := ((strHom k C).appLE ⊤ V' eV).hom
  have hft : ψ.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (strHom k C) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V', hV'a⟩ eV
  letI := ψ.toAlgebra
  obtain ⟨s, hs⟩ := hft.out

  have hconst : ∀ (p : Place k E) (c : Γ(Sp k, ⊤)), p.1 (f (ψ c)) ≤ 1 := by
    intro p c
    have hxs : ⊤ ≤ (x ≫ strHom k C) ⁻¹ᵁ (⊤ : (Sp k).Opens) := top_le_preimage_comp' x (strHom k C) ⊤ (fun _ _ => trivial)
    have htop : ⊤ ≤ (𝟙 (Sp k)) ⁻¹ᵁ (⊤ : (Sp k).Opens) := fun _ _ => trivial
    have h1 : evAt x hxV' (ψ c) = evAt (x ≫ strHom k C) hxs c :=
      (ev2 K C (Sp k) x (strHom k C) V' ⊤ hxV' _ eV c).symm
    have h2 : evAt (x ≫ strHom k C) hxs c =
        evAt (spMap (algebraMap k K) ≫ 𝟙 (Sp k)) (top_le_preimage_comp' _ _ _ htop) c :=
      evAt_congr' (by rw [Category.comp_id]; exact hx.2.2) _ _ c
    have h3 := ev1 k K (Sp k) (algebraMap k K) (𝟙 (Sp k)) ⊤ htop (top_le_preimage_comp' _ _ _ htop) c
    have hf : f (ψ c) = algebraMap k E (evAt (𝟙 (Sp k)) htop c) := by
      simp only [f, RingHom.comp_apply]
      rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply]
    rw [hf]
    by_cases hd : evAt (𝟙 (Sp k)) htop c = 0
    · rw [hd, map_zero, map_zero]; exact zero_le'
    · exact (p.2.2 _ hd).le
  have key : ∀ p : Place k E, (∀ a ∈ s, p.1 (f a) ≤ 1) → ∀ g, p.1 (f g) ≤ 1 := by
    intro p hp g
    have hg : g ∈ Algebra.adjoin Γ(Sp k, ⊤) (s : Set Γ(C, V')) := by rw [hs]; trivial
    induction hg using Algebra.adjoin_induction with
    | mem a ha => exact hp a ha
    | algebraMap c => exact hconst p c
    | add a b _ _ ha hb => rw [map_add]; exact (p.1.map_add _ _).trans (max_le ha hb)
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact mul_le_one' ha hb
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  refine ((s.finite_toSet.biUnion fun a _ => (?_ : {p : Place k E | ¬ p.1 (f a) ≤ 1}.Finite))).subset ?_
  · by_cases h0 : f a = 0
    · convert Set.finite_empty
      ext p; simp [h0]
    · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (f a) h0).1.subset fun p hp h1 => hp h1.le
  · rintro p ⟨b, hb1, hb2⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hno
    push_neg at hno
    have hall := key p fun a ha => hno a ha
    have hmem : ∀ g, f g ∈ p.O := fun g => (Valuation.mem_valuationSubring_iff _ _).2 (hall g)
    let φ : Γ(C, V') →+* p.O := f.codRestrict p.O hmem
    obtain ⟨b', hb', hev⟩ := ev6 p.O C V' hV'a φ
    have hc := top_le_preimage_comp' (spMap p.O.subtype) b' V' hb'
    have hd := top_le_preimage_comp' (spMap (algebraMap K E)) x V' hxV'
    have hcd : spMap p.O.subtype ≫ b' = spMap (algebraMap K E) ≫ x := by
      refine ev5 E C _ _ V' hV'a hc hd ?_
      ext g
      rw [ev1 p.O E C p.O.subtype b' V' hb' hc g, ev1 K E C (algebraMap K E) x V' hxV' hd g, hev]
      rfl
    have hbb := (GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K E C x hx p).unique hb1 hcd
    subst hbb
    exact hb2 fun w hw => hV'V (hb' hw)

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypesSeparatedByInertPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

theorem typesSep3_of_pin : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ((∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → A3.fam3.TypesSep3 := by
  intro hP hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hOk hCW hEx hJ hPin hPos hB
  have hSchur : SchurAll R.toRealDat := schurAll_of_cuspRapidDecay hP R.toRealDat
  have hTwo := GlobalTheory.T.exists_partner_combination_good_inert_lift hH R F hL hCW hEx hSchur
  have hAdj := GlobalTheory.AdjPart.adjoint_injective_on_part R hPos hB
  have hTr := GlobalTheory.T.exists_separating_inertPassage_carried_by_forms R F hL hOk hCW hEx hSchur hTwo hJ hAdj
  have hI := (hPin hTr).2
  exact A3.fam3.typesSep3_of (hOk.ok2.what₂ A3.fam3.F.μ0).comm
    (GlobalTheory.FamSep.typesSep_of_ok_isFam R.toRealDat hOk.ok2 hCW.base.fam) hI

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOne
section
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPairs

open Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj

theorem conjPl_eq_plMap {D : D7} [IsCMField D.host.E] (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.DivisionValues.conjPl P = plMap conjE P := by
  apply HeightOneSpectrum.ext
  rw [asIdeal_plMap]
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = _
  congr 1
  refine RingEquiv.ext fun x => RingOfIntegers.ext ?_
  rfl

theorem conjE_symm {E : Type} [Field E] [NumberField E] [IsCMField E] : (conjE (E := E)).symm = conjE :=
  RingEquiv.ext fun x => by rw [conjE_symm_apply, conjE_apply]

theorem finprod_val_nu_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T},
    Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E))
      (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  set ν := nuH G μ₀ i j with hν
  have hT : TrivOnF ν := (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1.2.1
  set c : HeightOneSpectrum (𝓞 D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun P => Formalism.DivisionValues.conjPl P with hcdef
  have hc : ∀ P, c P = plMap conjE P := fun P => conjPl_eq_plMap P
  have hcc : ∀ P, c (c P) = P := fun P => by
    rw [hc, hc]
    have h := plMap_symm_plMap (conjE (E := D.host.E)) P
    rwa [conjE_symm] at h
  have hcinj : Function.Injective c := fun x y h => by rw [← hcc x, h, hcc y]
  have hunr : ∀ P, ν.UnrAt P ↔ ν.UnrAt (c P) := fun P => by
    rw [hc, ← unrAt_inv_iff ν hT P]
    simp only [HChar.UnrAt, HChar.loc_inv, inv_eq_one]
  have hval : ∀ P, ν.UnrAt P → ((ν.val P : ℂˣ) : ℂ) * ((ν.val (c P) : ℂˣ) : ℂ) = 1 := fun P hP => by
    have h1 := val_inv_eq ν hT P (by rw [← hc]; exact (hunr P).1 hP)
    rw [HChar.val_inv] at h1
    rw [hc, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set Q' := (Lc.Q t).filter fun P => ν.UnrAt P with hQ'
  have hset : {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w} = (↑(Q' ∪ Q'.image c) : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe, hQ',
      Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (hL.Q_ram t w).1 h1 with h | ⟨P, hP, hcP⟩
      · exact Or.inl ⟨h, h2⟩
      · have e : w = c P := GlobalTheory.GoodPrimes.isConjPl_iff.1 hcP
        exact Or.inr ⟨P, ⟨hP, (hunr P).2 (e ▸ h2)⟩, e.symm⟩
    · rintro (⟨h, h2⟩ | ⟨P, ⟨hP, h2⟩, rfl⟩)
      · exact ⟨(hL.Q_ram t w).2 (Or.inl h), h2⟩
      · exact ⟨(hL.Q_ram t (c P)).2 (Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl⟩), (hunr P).1 h2⟩
  have hdisj : Disjoint Q' (Q'.image c) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨P', hP'Q, e⟩ := Finset.mem_image.1 hP'
    exact ((hL.Q_pl t) P' (Finset.mem_filter.1 hP'Q).1).2 P (Finset.mem_filter.1 hP).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 e.symm)
  show ∏ᶠ w ∈ {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w}, ((ν.val w : ℂˣ) : ℂ) = 1
  rw [hset, finprod_mem_coe_finset, Finset.prod_union hdisj, Finset.prod_image fun x _ y _ h => hcinj h,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun P hP => hval P (Finset.mem_filter.1 hP).2

end GlobalTheory.TwistPairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChange
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.FlatChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical in

theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) = if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  classical
  show (wtOf Dw (flatWt Dw τ) 0).1 (σ, (i : ℕ)) = _
  have hi := i.2
  by_cases h : σ (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_big (flatWt Dw τ) 0 ⟨σ, h⟩ i hp
    refine e0.trans ?_
    have hne : σ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
    by_cases e : σ = τ.1
    · have : (⟨σ, h⟩ : Psi H) = τ := Subtype.ext e
      simp [flatWt, parWt, this, e]
    · have : (⟨σ, h⟩ : Psi H) ≠ τ := fun e' => e (congrArg Subtype.val e')
      simp [flatWt, parWt, this, e, hne]
  · have h' := conj_mem h
    have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_small (flatWt Dw τ) 0 ⟨conjEmb σ, h'⟩ i hq
    simp only [conjEmb_conjEmb] at e0
    refine e0.trans ?_
    have hne : σ ≠ τ.1 := fun e' => h (e' ▸ τ.2)
    have hiff : (⟨conjEmb σ, h'⟩ : Psi H) = τ ↔ σ = conjEmb τ.1 := by
      constructor
      · intro e'; rw [← congrArg Subtype.val e', conjEmb_conjEmb]
      · intro e'; apply Subtype.ext; show conjEmb σ = τ.1; rw [e', conjEmb_conjEmb]
    by_cases e : σ = conjEmb τ.1
    · have h2 := hiff.2 e
      rw [if_neg hne, if_pos e]
      simp only [flatWt, parWt, if_pos h2]
      norm_num
    · have : (⟨conjEmb σ, h'⟩ : Psi H) ≠ τ := fun e' => e (hiff.1 e')
      simp [flatWt, parWt, this, e, hne]

theorem flatWt_char (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ) :
    (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) =
      ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)
  have key : (∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i) =
      (∏ i : Fin (Dw.mult τ.1), t (some ⟨τ.1, i⟩))⁻¹ * ∏ j : Fin (Dw.mult (conjEmb τ.1)), t (some ⟨conjEmb τ.1, j⟩) := by
    rw [Fintype.prod_option, Fintype.prod_sigma]
    have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
    rw [h0, zpow_zero, one_mul]
    rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_]
    · congr 1
      · rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_pos rfl, zpow_neg_one]
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_neg hne.symm, if_pos rfl, zpow_one]
    · rintro σ ⟨h1, h2⟩
      refine Finset.prod_eq_one fun i _ => ?_
      rw [exOf_flatWt_some, if_neg h1, if_neg h2, zpow_zero]
  rw [key, ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
  congr 1
  rw [mul_comm, mul_inv_cancel_left]

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ), (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := @flatWt_char

end GlobalTheory.FlatChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPoint
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatPointNe

theorem evR_sig_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → evR Xo c s.sig y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x _ Z τ s K _ _ _ y hy h0
  have ht : Tested y := GlobalTheory.FlagTan.fromTest_of_isLocalRing y
  have h1 : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
    rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem hy ht]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.FlatPointNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets | exact GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets | (intros; apply GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHom
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem path_bc_ring {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] {R' : Type} [CommRing R']
    (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) (h : IsPath G c b ξ) :
    IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) := by
  have hC : ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.C (R := R)) =
      (PowerSeries.C (R := R')).comp φ := by
    ext a n
    simp [PowerSeries.coeff_C]
    split_ifs <;> simp_all
  have h0 : (PowerSeries.constantCoeff (R := R')).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      φ.comp (PowerSeries.constantCoeff (R := R)) := by
    ext p
    simp only [RingHom.comp_apply]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    simp
  have hs : (PowerSeries.rescale (φ c)).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.rescale c) := by
    ext p n
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, h.base, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hC,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.zero, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.scale, Category.assoc]

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    unitSec G ≫ q.left = unitSec H := by
  show (η[G]).left ≫ q.left = (η[H]).left
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem sqr_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    sqr G ≫ q.left = q.left ≫ sqr H := by
  unfold sqr
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id]

end GlobalTheory.Nef

theorem GlobalTheory.Nef.paths_bc : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  refine ⟨?_, ?_⟩
  · intro S G _ R _ R' _ φ c u b ξ h
    refine ⟨path_bc_ring G φ c u b ξ h, ?_⟩
    intro _ n V τ w _ U hU ht hU' V' hV he hb f
    rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 (PowerSeries R) (PowerSeries R') G.left ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ξ U hU hU' f]
    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map, ht U hU V' hV he hb f, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pow_one, ← _root_.mul_assoc]
  · intro S G H _ _ q _ R _ c b ξ
    refine ⟨fun h => ⟨?_, ?_, ?_⟩, ?_, sqr_comp q⟩
    · rw [Category.assoc, Over.w q, h.base]
    · rw [← Category.assoc, h.zero, Category.assoc, unitSec_comp]
    · rw [← Category.assoc, h.scale, Category.assoc, Category.assoc, sqr_comp]
    · rw [triv, Category.assoc, Category.assoc, unitSec_comp, triv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridUnr

theorem chi_eta_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  intro D T Lc sc G μ₀ hμ t v e he hv i
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine ⟨GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ h1 h2) v e he fun P hP => ?_,
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hμ.eta v e he fun P _ => Lc.C.isEta.unr P⟩
  exact G.ch.unr _ h1 h2 P (by rw [hP]; exact hv)

end GlobalTheory.GridUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientDataStatement
section
open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  first | exact @GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | exact GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | (intros; apply GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' <;> assumption)
end

