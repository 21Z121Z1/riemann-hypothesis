import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem perfectField_fractionRing_zmod (p : ℕ) [Fact p.Prime] :
    PerfectField (FractionRing (ZMod p)) :=
  PerfectField.of_ringEquiv (FractionRing.algEquiv (ZMod p) (ZMod p)).symm.toRingEquiv

theorem formalFibre_isRegularRing_of_essFiniteType_int :
    ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K]
      [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro R K _ _ _ _ _ _
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  ·
    set p := ringChar K with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℤ R
    have hpK : algebraMap R K (p : R) = 0 := by
      rw [map_natCast]; exact CharP.cast_eq_zero K p
    have hnu : ((p : ℕ) : R) ∈ nonunits R := fun hu => by
      have := hu.map (algebraMap R K); rw [hpK] at this; exact not_isUnit_zero this
    let I : Ideal R := Ideal.span {((p : ℕ) : R)}
    haveI : CharP (R ⧸ I) p := CharP.quotient R p hnu
    have hI : I ≠ ⊤ := by
      exact fun h => hnu (Ideal.span_singleton_eq_top.mp h)
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hker : I ≤ RingHom.ker (algebraMap R K) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpK
    letI : Algebra (R ⧸ I) K := (Ideal.Quotient.lift I (algebraMap R K) hker).toAlgebra
    haveI : IsScalarTower R (R ⧸ I) K := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.EssFiniteType R (R ⧸ I) :=
      Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
    haveI : Algebra.EssFiniteType ℤ (R ⧸ I) := Algebra.EssFiniteType.comp ℤ R (R ⧸ I)
    letI : Algebra (ZMod p) (R ⧸ I) := ZMod.algebra (R ⧸ I) p
    haveI : Algebra.EssFiniteType (ZMod p) (R ⧸ I) := Algebra.EssFiniteType.of_comp ℤ (ZMod p) (R ⧸ I)
    haveI : Algebra.EssFiniteType (R ⧸ I) K := Algebra.EssFiniteType.of_comp R (R ⧸ I) K
    haveI := perfectField_fractionRing_zmod p
    have hinj : ∀ a : ZMod p, algebraMap (R ⧸ I) K (algebraMap (ZMod p) (R ⧸ I) a) = 0 → a = 0 :=
      fun a ha => ((algebraMap (R ⧸ I) K).comp (algebraMap (ZMod p) (R ⧸ I))).injective
        (by simpa using ha)
    have hreg := GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType (ZMod p) (R ⧸ I) K hinj
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective R (R ⧸ I) K Ideal.Quotient.mk_surjective
    exact IsRegularRing.of_ringEquiv e
  ·
    haveI : CharP K 0 := by rw [← h0]; exact ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    refine GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType ℤ R K ?_
    intro a ha
    rw [eq_intCast (algebraMap ℤ R), map_intCast] at ha
    exact_mod_cast ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobeniusStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ), frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) := by
  first | exact @GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob | exact GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob | (intros; apply GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FubiniStudyPull

theorem fubiniStudy_pullback_chern_mass_eq_degree : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim)
    (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str),
    Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ
      (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  intro Y π hπ
  obtain ⟨hPI, hPdim, hPproj, hPsm⟩ := GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim ℂ Y.dim
  haveI := hPI
  by_cases hη : π (genericPoint Y.X) = genericPoint (PSpace ℂ Y.dim)
  · have hδ := GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim Y.topologicalKrullDim_eq π hπ hη
    have hm := fun ε => GlobalTheory.T.chernMass_pull_mul_degree_field ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str (RingHom.id ℂ)
      Y.dim hPproj Y.isProjOver hPsm π hπ hη hδ (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).B
      ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)) ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf _) ε
    obtain ⟨h1, h0⟩ := GlobalTheory.T.chern_form_fubini_study_total Y.dim
    have hi := GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim.le π hπ hη hδ (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    have ht := GlobalTheory.T.top_self_intersection_O1_projective ℂ Y.dim
    rw [GdegPullProof.chernInt_one, hm 1, hm (-1), h1, h0]
    change _ = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hi, ht]
    simp
  · have hc := GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes Y π hπ ⟨genericPoint (PSpace ℂ Y.dim), fun h =>
      hη (h.antisymm (genericPoint_specializes _)).eq⟩
    have hn := GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim Y.isProjOver
      hPdim.le Y.topologicalKrullDim_eq.le π hη (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    rw [hc]
    change (0 : ℝ) = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hn]
    simp

end GlobalTheory.FubiniStudyPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLevelSelfDualLatticeStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_level_self_dual_lattice : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), 2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f ∧ (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  first | exact @GlobalTheory.CovTop.MassBridge.mass_bridge | exact GlobalTheory.CovTop.MassBridge.mass_bridge | (intros; apply GlobalTheory.CovTop.MassBridge.mass_bridge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.LabTrans GlobalTheory.SeriesCompare GlobalTheory.ArcPull

theorem recognition_core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  intro R _ _ _ hR D A lab n hn ho hu hT hgal htheta W _ _ _ hW φ iφ lφ G' _ _ D' A' U' a hG' hfib
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩

  obtain ⟨W₀, _, _, _, φ₀, G₀, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG₀, fib₀, c₀, H₀⟩ := hT
  have := hW₀.1
  have := hW₀.2.2
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  obtain ⟨g₀, hg₀, hg₀'⟩ := exists_goodLab b₀ hG₀ U₀ (Kb W₀)
  have Glab : GoodLab D.toPre A (Kb R) lab := by
    refine (goodLab_move h₀ c₀ em₀ D₀.tau_bimult fib₀ lab g₀ fun k hk p => ?_).2 hg₀
    obtain ⟨ga₀, hga₀, gp₀, -⟩ := fib₀
    obtain ⟨x, hx⟩ := exists_lift_pt gp₀.1 em₀.toRingHom
      (em₀.comp_algebraMap.trans (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
        (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (hga₀ r).symm)))) (lab k p)
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff h₀ c₀ em₀ D₀.tau_bimult p _).2 rfl
    rw [← (hg₀' k hk _ x).1 (H₀ k hk p p₁ _ x t₁ t₂ t₃ hx)]
    exact hx

  haveI := lφ
  obtain ⟨DW, ⟨hWp⟩⟩ := GlobalTheory.MumPull.exists_pull R W φ iφ lφ D
  have hBW := DW.tau_bimult
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := GlobalTheory.T.exists_complete_isAlgClosed_cExt' W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp (fracMap iφ)).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (fracMap_algebraMap iφ r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) C

  obtain ⟨ε, hε, -, -, -⟩ := exists_ptHom hfib cC em
  let fW : ∀ k, QkPt DW.toPre C k → (TFK (R := W) C ⟶ A'.A) := fun k q =>
    if hk : 1 ≤ k then ε (lab k ((Equiv.ofBijective _ (tr_bij hWp cC em hBW hk)).symm q)) else 1
  have hfW : ∀ k (hk : 1 ≤ k) p, fW k (tr hWp cC em hBW p) = ε (lab k p) := fun k hk p => by
    simp only [fW, dif_pos hk, Equiv.ofBijective_symm_apply_apply]
  have GW : GoodLab DW.toPre A' C fW := (goodLab_move hWp cC em hBW hfib lab fW fun k hk p => by
    rw [hfW k hk p]; exact (hε _ _).1 rfl).1 Glab
  obtain ⟨f', G'', hf'⟩ := exists_goodLab bW hG' U' C

  have hO : CExt W ⊥ C := ⟨hC.1, fun r hr => hC.2 r (bot_le (a := maximalIdeal W) hr)⟩
  have huW : IsUnit (n : W) := by simpa using hu.map φ
  have h1 : ‖(n : C)‖ = 1 := (isUnit_iff_norm hC n).1 huW
  have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨N₁, ν₁, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL W DW.toPre DW.psi_even hBW C ⊤ fun _ => trivial
  obtain ⟨N, ν, q₀, -, hIν, hq₀, -⟩ := exists_integral hW DW hC ν₁
  have hT := GlobalTheory.ValuesTorsion.tors_of_integral hL hL₂ (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) W DW.toPre DW.psi_even hBW C hO N ν hIν n hn
    ho h1
  have hd : ∀ g : N.Gt, ∃ g', g' ^ n = g := fun g => by
    obtain ⟨g', hg'⟩ := (GlobalTheory.Ex.QStr.qStructure C N n _ hnC hT 1).2.1 g
    exact ⟨g', by rw [← hg', pow_one]⟩
  have h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0 := by
    obtain ⟨h, -, -, hh⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q₀ hq₀ n _ hn ho h1 hT 1 le_rfl).2.2 1
    exact ⟨_, hh⟩
  obtain ⟨N', ν', -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial

  have galW : ∀ k, (∃ j, k = n ^ j) → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C k),
      QkExt (σ : C →+* C) p pσ → (fW k pσ).left = spMap (σ : C →+* C) ≫ (fW k p).left := by
    rintro k ⟨j, rfl⟩ σ p pσ hp
    have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
    obtain ⟨p₀, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    let σR : C →ₐ[FractionRing R] C := ⟨(σ : C →+* C), fun t => σ.commutes (fracMap iφ t)⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Kb R →ₐ[FractionRing R] Kb R, em.toRingHom.comp ρ.toRingHom = (σR.comp em).toRingHom := by
      letI : Algebra (Kb R) C := em.toRingHom.toAlgebra
      haveI : IsScalarTower (FractionRing R) (Kb R) C := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
      exact ⟨(σR.comp em).restrictNormal (Kb R), RingHom.ext fun x => (σR.comp em).restrictNormal_commutes (Kb R) x⟩
    obtain ⟨p₀ρ, hρp⟩ := exists_ext hB ρ p₀
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p₀ _).2 rfl
    obtain ⟨r, hr⟩ := exists_ext hB σR p₁
    have u₁ := qkExt_trans t₁ hr
    obtain ⟨r', hr'⟩ := exists_ext hB em p₀ρ
    have u₂ := qkExt_trans hρp hr'
    rw [hρ] at u₂
    obtain rfl := ext_unique hB (σR.comp em) u₁ u₂
    have e₁ : pσ = tr hWp cC em hBW p₀ρ := (lies_iff hWp cC em hBW p₀ρ pσ).1 ⟨r, hr', by
      rw [hp.1, t₂, hr.1], isPullGtF_ext hWp cC (σ : C →+* C) σ.toAlgHom.comp_algebraMap t₃ hr hp⟩
    rw [e₁, hfW _ hk, hfW _ hk]
    obtain ⟨ga, -, gpa, -⟩ := hfib
    apply gpa.1.hom_ext
    · rw [(hε _ _).1 rfl, Category.assoc, (hε _ _).1 rfl, hgal ρ j p₀ p₀ρ hρp, ← Category.assoc,
        ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, hρ]
      rfl
    · rw [Category.assoc, Over.w (ε (lab _ p₀ρ)), Over.w (ε (lab _ p₀))]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap σ.toAlgHom.comp_algebraMap)).symm
  have gal' : ∀ k, 1 ≤ k → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt D'.toPre C k),
      QkExt (σ : C →+* C) p pσ → (f' k pσ).left = spMap (σ : C →+* C) ≫ (f' k p).left := by
    intro k hk σ p pσ hp
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG' U' C C σ.toAlgHom k hk p
    obtain ⟨x', hx'⟩ := hx (f' k p)
    rw [← (hf' k hk pσ x').1 ((hiff pσ (f' k p) x' hp hx').1 ((hf' k hk p _).2 rfl))]
    exact hx'
  have gal : ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C ((n ^ 1) ^ 2))
      (p' pσ' : QkPt D'.toPre C ((n ^ 1) ^ 2)), QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' →
      fW _ p = f' _ p' → fW _ pσ = f' _ pσ' := fun σ p pσ p' pσ' h₁ h₂ h₃ =>
    Over.OverMorphism.ext (by
      rw [galW _ ⟨2, by ring⟩ σ p pσ h₁, h₃, gal' _ (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)) σ p' pσ' h₂])

  have BG' := GlobalTheory.Ex.GtValues.points_correspond W D'.toPre D'.psi_even D'.tau_bimult C N' ν'
  have hc : ∀ j, ∃ c : Cˣ, ∀ p p' q q', ν.QPt p q → ν'.QPt p' q' → fW ((n ^ j) ^ 2) p = f' _ p' →
      N'.tx (n ^ j) q' = c * N.tx (n ^ j) q := by
    intro j
    have hm : Odd (n ^ j) := ho.pow
    have hk : 1 ≤ (n ^ j) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    have hum : IsUnit ((n ^ j : ℕ) : R) := by rw [Nat.cast_pow]; exact hu.pow j
    obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R hR D (n ^ j) hm hum _ id
    have Θ := htheta j v hv
    have hCR : CExt R (maximalIdeal R) C :=
      ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
    obtain ⟨N₀, ν₀, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
    obtain ⟨J, hJX, hJ⟩ := GlobalTheory.Mum.OneTraitTheta.exists_values_iso hL hWp cC ν₀ ν
    choose q₀ hq₀ using fun i : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) =>
      exists_val D.psi_even hB ν₀ (qkExt hB em.toRingHom em.comp_algebraMap i)
    obtain ⟨s, hs⟩ := hv C hCR em N₀ ν₀ (fun i => qkExt hB em.toRingHom em.comp_algebraMap i) q₀
      (fun i => (qkExt_iff hB _ em.comp_algebraMap _ _).2 rfl) hq₀
    choose pp hpp using fun i => G''.onto _ hk (fW _ (tr hWp cC em hBW i)) (GW.pow _ hk _)
    choose qq hqq using fun i => exists_val D'.psi_even D'.tau_bimult ν' (pp i)
    have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV GlobalTheory.T.torus_torsion_points_correspond_values (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G' hG' U' C hC N' ν' (n ^ j) hm _ pp qq
      (fun i => fW _ (tr hWp cC em hBW i)) (fun i => (hf' _ hk _ _).2 (hpp i).symm) hqq
    obtain ⟨c₃, hc₃⟩ := theta_prop hfib cC em hm (x := lab _) (x' := fun i => fW _ (tr hWp cC em hBW i))
      (fun i => by rw [hfW _ hk]; exact (hε _ _).1 rfl) (fun i => GW.pow _ hk _) Θ Q
    refine ⟨c₃ * s * J.lam, fun p p' q q' hp hp' hpp' => ?_⟩
    obtain ⟨i, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW i _).2 rfl
    obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
    have e₁ : N'.tx (n ^ j) (qq i) = N'.tx (n ^ j) q' :=
      GlobalTheory.ModelData.Scalar.tx_congr N' hm (((BG'.2.2.2.2 _).2.2 _ _ _ _ (hqq i) hp').1
        ((G''.eqv _ hk _ _).1 ((hpp i).trans hpp')))
    have e₂ := (GlobalTheory.RelabelCoords.series_iso J hm (p := q) (p' := q₀ i) (ν₀.eX.injective (by
      rw [hJX, hp.1, t₂, AddEquiv.apply_symm_apply]; exact (hq₀ i).1)) (hJ _ _ _ _ (hq₀ i).2 hp.2 t₃)).1
    rw [← e₁, hc₃ i, hs i, e₂, Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc,
      Units.mul_inv_cancel_left]

  obtain ⟨e, he⟩ := rec_trait hW hC ν ν' GW G'' hn ho huW hd gal hc h0
  obtain ⟨hD, T⟩ := GlobalTheory.LabTrans.exists_comp iφ Function.injective_id hWp e
  refine ⟨hD, C, inferInstance, inferInstance, inferInstance, inferInstance, em, cC, fun j p p₁ p'' x' h₁ h₂ h₃ h₄ => ?_⟩
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  refine (hf' _ hk p'' x').2 ?_
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 h₁
  rw [(hε _ _).2 h₄, ← hfW _ hk p]
  obtain ⟨p₁', t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p _).2 rfl
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
  have cI : Compat (RingHom.id W) C := fun _ => rfl
  have g₁ := T.isPullGtF cC t₃ (isPullGtF_pullGt e hGF cI (tr hWp cC em hBW p).g)
  have g₂ := pullGt_unique hD cC g₁ h₃
  refine he j _ _ ?_ ?_
  · apply hD.xe.injective
    rw [h₂, AddEquiv.apply_symm_apply, ← T.xe_eq, AddEquiv.apply_symm_apply, t₂, AddEquiv.apply_symm_apply]
  · rw [← g₂]
    exact isPullGtF_pullGt e hGF cI _

end GlobalTheory.Mum.Recog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisQuotient_smooth_baseChange_iso_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ)) := by
  first | exact @GlobalTheory.Mum.quotient_smooth_and_baseChange_iso | exact GlobalTheory.Mum.quotient_smooth_and_baseChange_iso | (intros; apply GlobalTheory.Mum.quotient_smooth_and_baseChange_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPowStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  first | exact @GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow | exact GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow | (intros; apply GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFirstChernFormsPullbackCell
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GradedPull

theorem ratVal_zero' {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem ofValues_ddc_eq {n : ℕ} {p u : V n → ℝ} {Φ : V n → V n} {g : V n → ℂ} {z w : V n} (hw : Φ z = w)
    (hu : ContDiffAt ℝ 2 u w) (hΦ : ContDiffAt ℂ 2 Φ z) (hg : ∀ᶠ v in 𝓝 z, DifferentiableAt ℂ g v) (h0 : g z ≠ 0)
    (h : p =ᶠ[𝓝 z] fun v => u (Φ v) - Real.log (‖g v‖ ^ 2)) :
    (ofValues (ddc p z) : Alt n) = pull (fderiv ℂ Φ z) (ofValues (ddc u w) : Ev n) := by
  subst hw
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 hg
  have hg2 : ContDiffAt ℂ 2 g z := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hUo
    fun v hv => (hU v hv).differentiableWithinAt).contDiffAt (hUo.mem_nhds hz)).of_le (by norm_cast)
  have hs : IsSesq (ddc u (Φ z)) := by
    constructor <;> intros <;> simp [ddc] <;> ring
  rw [GlobalTheory.SecForm.pull_ofValues _ _ hs]
  congr 2
  funext ξ η
  have h1 : ContDiffAt ℝ 2 (fun v => u (Φ v)) z := hu.comp z (hΦ.restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (‖g v‖ ^ 2)) z :=
    ((hg2.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  rw [ddc, ddc, leviForm_congr h, leviForm_sub h1 h2, leviForm_log_normSq_eq_zero hg2 h0, sub_zero,
    leviForm_comp_holo hu hΦ]

theorem grF_eq_pull : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ∀ r : Root m, (grF E' (pullGram E H φ f hf) r x : Alt Y.dim) = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (ofValues (ddc (cellPot ε (fun v => H A (c.e.symm v)) r) (cellMap ε f hf c u x.pt)) : Ev Y.dim) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u H hH ε x hx r
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  set B₀ := (E'.nonempty (under x.pt)).choose with hB₀
  have hB₀m : B₀ ∈ E'.S (under x.pt) := (E'.nonempty (under x.pt)).choose_spec
  set B := upM u * A.map φ with hB
  have hT : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      HolUnitAt (atlas Y σ) (fun z => ((B₀ * B⁻¹) r.1).map (ratVal · z)) w ∧
      ∀ i j : Fin (m r.1), i < j → ((B₀ * B⁻¹) r.1).map (ratVal · w) i j = 0 := by
    intro w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) r.1
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y (m r.1) ((B₀ * B⁻¹) r.1) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero' w
  have hne : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      ((B₀ * B⁻¹) r.1).map (ratVal · w) r.2 r.2 ≠ 0 := fun w h1 h2 => by
    obtain ⟨hol, tri⟩ := hT w h1 h2
    have := hol.1.ne_zero
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)] at this
    exact Finset.prod_ne_zero_iff.1 this r.2 (Finset.mem_univ _)
  have hπ : Continuous (ptMap σ f hf) := by
    unfold ptMap
    apply GlobalTheory.Points.PtsOver.continuous_map
  have hAπ : A ∈ E.S (under (ptMap σ f hf x.pt)) := hx.1.1
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ A hAπ r.1).2 c hx.2).self_of_nhds
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hu := (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m Y.dim X.dim ε (fun v => H A (c.e.symm v)) (cellMap ε f hf c u x.pt) r
    (by rw [hb]; exact hsm.2) (by rw [hb]; exact fun i j => (hsm.1 i j).of_le (by norm_cast))).1
  have hl : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ht : Tendsto x.ch.symm (𝓝 x.crd) (𝓝 x.pt) := by
    have := x.ch.continuousAt_symm (x.ch.map_source x.2)
    rwa [ContinuousAt, x.ch.left_inv x.2] at this
  have e1 : ∀ᶠ z in 𝓝 x.pt, InCell E E' φ f A u (under z) :=
    (isOpen_ptsIn (p := Y.str) (σ := σ) ⟨_, (GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u).1⟩).mem_nhds (mem_ptsIn.2 hx.1)
      |> fun h => Filter.mem_of_superset h fun z hz => mem_ptsIn.1 hz
  have e2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' x.pt B₀ hB₀m
  have e3 : ∀ᶠ z in 𝓝 x.pt, ptMap σ f hf z ∈ c.e.source := hπ.continuousAt.eventually (c.e.open_source.mem_nhds hx.2)
  refine ofValues_ddc_eq (g := fun v => ((B₀ * B⁻¹) r.1).map (ratVal · (x.ch.symm v)) r.2 r.2)
    (congrArg (cellMap ε f hf c u) hl) hu (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u _ ε x hx)
    ((hT _ hx.1.2 hB₀m).1.2 x.1.1 x.2 r.2 r.2) (by rw [hl]; exact hne _ hx.1.2 hB₀m) ?_
  filter_upwards [ht.eventually e1, ht.eventually e2, ht.eventually e3] with v h1 h2 h3
  obtain ⟨hol, tri⟩ := hT _ h1.2 h2
  have hpd := hM.posDef _ B h1.2 r.1
  have e := hM.trans _ B h1.2 B₀ h2 r.1
  have e' := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ hpd tri hol.1).2 r.2
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 r.2).1
  have eg := congrFun (GlobalTheory.T.pullGram_flagCell_frame F σ X Y ι m E E' φ f hf hR c A u H hH _ h1) r.1
  have ec : cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) =
      -Real.log (grD (pullGram E H φ f hf B (x.ch.symm v) r.1) r.2) := by
    rw [hB, eg, cellPot, cellMap, bsL_pt, fb_pt, c.e.left_inv h3]
  show -Real.log (grD (pullGram E H φ f hf B₀ (x.ch.symm v) r.1) r.2) =
    cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) - _
  rw [ec, e]
  erw [e']
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne _ h1.2 h2))) hpos.ne']
  ring

end GlobalTheory.FlagCell2.GradedPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrameStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramConnectionPair_chernFields_local_frame : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ (x : A.Pt) (k : ℕ), ∀ᶠ v in 𝓝 x.crd, A.loc (fld A (powFld A G k)) x.1.1 v = powAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (fld A (chernFld A G k)) x.1.1 v = chernAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (transFld A G G' k) x.1.1 v = transAt (fun u => G x.pt (x.ch.symm u)) (fun u => G' x.pt (x.ch.symm u)) v k := by
  first | exact @GlobalTheory.ChernCalc.loc_fields_near | exact GlobalTheory.ChernCalc.loc_fields_near | (intros; apply GlobalTheory.ChernCalc.loc_fields_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSumStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_isHermitian_l2_eq_double_sum : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).IsHermitian ∧ ∀ c : ι → ℂ, (∀ σ, Integrable (cmb v c σ) (μ σ)) ∧ 0 ≤ l2 μ v c ∧ (l2 μ v c : ℂ) = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * gram μ v i j := by
  first | exact @GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | exact GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | (intros; apply GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  first | (exact @GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (exact GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (intros; apply GlobalTheory.HTQuotRigid.eq_one_of_fixes_point  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → HasPolChart F s j e φ BD d x → HasChart F s j e φ BD d x := by
  first | exact @GlobalTheory.PolDeg.hasChart_of_hasPolChart | exact GlobalTheory.PolDeg.hasChart_of_hasPolChart | (intros; apply GlobalTheory.PolDeg.hasChart_of_hasPolChart <;> assumption)
end

