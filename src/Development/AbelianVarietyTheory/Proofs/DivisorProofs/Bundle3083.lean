import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDegDataIsoOfGaloisDescendedGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagConcatenationExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
import GroundTheory.GlobalFields.Adele.Approximation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslatiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.same_lam_iff_locally_triv | exact GlobalTheory.TwistFlat.same_lam_iff_locally_triv | (intros; apply GlobalTheory.TwistFlat.same_lam_iff_locally_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumFam.lbIso_lam_retract_adj | exact GlobalTheory.MumFam.lbIso_lam_retract_adj | (intros; apply GlobalTheory.MumFam.lbIso_lam_retract_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeatLevelActionUnipotent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem eqvLin_pull : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed Xo c → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF I g hI hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hPr hO hj heq
  obtain ⟨m, hm, hmv⟩ := GlobalTheory.T.level_automorphism_integral_map hP E H Dw l Xo c TF Z hpq hA Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq
  have hT := GlobalTheory.T.torsion_fibre_injects_levelModule E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq m hm hmv
  exact ⟨pullG TF Z φ, inferInstance, pullψ TF Z φ, pullAct TF Z φ, m,
    isGrpPullback_pullψ TF Z φ, pullAct_pullψ TF Z φ, hm.1, hm.2.1, hm.2.2,
    GlobalTheory.T.fibre_action_trivial_of_fixed_point_residue_field E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι hU X' φ ρ' hN hPr m hm hT⟩

end GlobalTheory.EqvAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreOfNormsPowerStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_fibre_of_norms_power : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y), A.NefFib → ∀ (V : Cover Y) (L : HermLB V.p) (k : ℕ), 0 < k → Norms V L (fun x => genAt A.D x ^ k) (fun σ y => k * lnAdl A σ y) (fun v e y => k * A.lg v e y) → NefFib L := by
  first | exact @GlobalTheory.CoverNef.nefFib_of_norms_adl | exact GlobalTheory.CoverNef.nefFib_of_norms_adl | (intros; apply GlobalTheory.CoverNef.nefFib_of_norms_adl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
  GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefGeneric

theorem ratDeg_nonneg : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q),
    IsArithVar q 1 → ArInt.NefFib L → 0 ≤ ratDeg q L.B := by
  intro k _ W q L hW hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1, e2⟩ := GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective k W q 1 hW 2 L.B L.isLB
  obtain ⟨hproj, hdim⟩ := GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one k W q hW 2
  letI := GlobalTheory.algebraΓOfHom
    (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod 2))))
  have h := GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod 2 _ hproj hdim _ (LB.isLB_pull L.isLB _)
    (fun Z i _ _ _ hZ => GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres k W q L 2 hL Z i hZ)
  rw [ratDeg, degOfRank, ← e1, ← e2]
  simpa [degOfRank] using h

theorem isNef_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (L : HermLB P.p),
    ArInt.NefFib L → IsNef F (L.B.pull P.j) := by
  intro F _ _ Y P L hL
  refine ⟨LB.isLB_pull L.isLB P.j, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hz, hpb⟩ := GlobalTheory.T.complete_curve_arith_model_closure F Y P Z hZ
  have e := GlobalTheory.T.curve_model_rational_degree F Y P Z hZ W w z hW hz hpb L.B L.isLB
  have h0 := ratDeg_nonneg (𝓞 F) W (w ≫ P.p) (L.pull w rfl) hW
    (ArInt.nefFib_pull (𝓞 F) P.X W P.p (w ≫ P.p) P.ar.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ P.p) (L.B.pull w) at h0
  rw [e] at h0
  have hpos : (0 : ℤ) < (Module.finrank ℚ F : ℤ) := by exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h0

end GlobalTheory.NefGeneric

theorem GlobalTheory.CovHt.Link.nef_of_semiPos_nefFib : Hypotheses2 → HypothesesH → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F)
    (Y : Var F) (M : Adl C Y), M.SemiPos → M.NefFib → Y.nef M.D := by
  intro _ _ F _ _ C Y M _ ⟨P, L, k, cf, ⟨_, r, hr, _⟩, hL⟩
  have h := GlobalTheory.NefGeneric.isNef_model F Y P L hL
  exact (Var.nef_nsmul_iff k.pos).1 ((Var.nef_iff_of_toPic_eq _ hr.toPic_eq).2 h)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨hne, hdiv⟩ := ha
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  have hu0 : algebraMap o Ω (u : o) ≠ 0 := by
    intro h0
    have h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1 := by simp
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) := by
    have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
    rw [hv, hu, map_mul, hi]
    field_simp
  rw [key]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))

end GlobalTheory.Poinc.Sep.SupISymm

open GlobalTheory.Poinc.Sep.SupISymm in

theorem GlobalTheory.Poinc.Sep.neg_mem_supI : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro g n F W Z i X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.T.realisedThetaSystem_thetaConstant_neg_even_upToRoot X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDegDataIsoOfGaloisDescendedGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_degData_iso_of_galoisDescendedGroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → Nonempty (IsPullDeg (RingHom.id R) D₁.toPre D.toPre) := by
  first | exact @GlobalTheory.Mum.nonempty_isPullDeg_of_galAct | exact GlobalTheory.Mum.nonempty_isPullDeg_of_galAct | (intros; apply GlobalTheory.Mum.nonempty_isPullDeg_of_galAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFlagPullback
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.CovTest

namespace GlobalTheory.FlagTwoSteps

theorem nonempty_flag_pullback {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] {r : ℕ}
    {W U : X.Opens} {e : Fin r → Γ(F, W)} (he : IsFrame e) (hU : U ≤ W) :
    Nonempty (Vert.Flag ((Scheme.Modules.pullback U.ι).obj F) r) := by
  have h1 := (he.res hU).pullback U.ι
  have h2 : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun y _ => by simp
  exact Vert.Flag.nonempty_of_isFrame_top r _ _ (h1.res h2)

theorem shortExact_pullback {X : Scheme.{0}} (U : X.Opens) {A B : X.Modules} {s : A ⟶ B}
    {r : ℕ} (hA : IsVB A r) (hs : IsSubbundle s) :
    ∃ h : (Scheme.Modules.pullback U.ι).map s ≫ cokernel.π ((Scheme.Modules.pullback U.ι).map s) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have := (GlobalTheory.SubPull.isSubbundle_pullback X U.toScheme U.ι A B s r hA hs).mono
  exact ⟨cokernel.condition _, { exact := ShortComplex.exact_cokernel _ }⟩

theorem exists_flag_two_steps : ∀ (X : Scheme.{0}) (E S P : X.Modules) (n m₁ m₂ : ℕ) (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ n) (s : S ⟶ P) (j : P ⟶ E), IsVB E n → IsVB S m₁ → IsVB P m₂ → IsSubbundle s →
    IsSubbundle j → ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (fl : GlobalTheory.Vert.Flag ((Scheme.Modules.pullback U.ι).obj E) n)
      (eS : (Scheme.Modules.pullback U.ι).obj S ≅ fl.F ⟨m₁, by omega⟩)
      (eP : (Scheme.Modules.pullback U.ι).obj P ≅ fl.F ⟨m₂, by omega⟩),
      eS.hom ≫ fl.ι ⟨m₁, by omega⟩ = (Scheme.Modules.pullback U.ι).map (s ≫ j) ∧
        eP.hom ≫ fl.ι ⟨m₂, by omega⟩ = (Scheme.Modules.pullback U.ι).map j := by
  intro X E S P n m₁ m₂ h₁₂ h₂ s j hE hS hP hs hj x
  have : Nonempty X := ⟨x⟩
  have := hs.mono
  have := hj.mono
  obtain ⟨a, ha⟩ := hs.isVB_cokernel
  obtain ⟨b, hb⟩ := hj.isVB_cokernel
  have hSE₁ : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
    { exact := ShortComplex.exact_cokernel s }
  have hSE₂ : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_cokernel j }
  obtain rfl : m₂ = m₁ + a := hP.rank_unique (VBExt.isVB_X₂_of_shortExact X _ m₁ a hSE₁ hS ha)
  obtain rfl : n = m₁ + a + b := hE.rank_unique (VBExt.isVB_X₂_of_shortExact X _ _ b hSE₂ hP hb)
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hS x
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := ha x
  obtain ⟨U₃, e₃, hx₃, he₃⟩ := hb x
  let U : X.Opens := U₁ ⊓ U₂ ⊓ U₃
  have hxU : x ∈ U := ⟨⟨hx₁, hx₂⟩, hx₃⟩
  have := hS.isQuasicoherent
  have := ha.isQuasicoherent
  have := hb.isQuasicoherent
  obtain ⟨flS⟩ := nonempty_flag_pullback (U := U) he₁ (inf_le_left.trans inf_le_left)
  obtain ⟨flA⟩ := nonempty_flag_pullback (U := U) he₂ (inf_le_left.trans inf_le_right)
  obtain ⟨flB⟩ := nonempty_flag_pullback (U := U) he₃ inf_le_right
  set Φ := Scheme.Modules.pullback U.ι
  obtain ⟨z₁, hz₁⟩ := shortExact_pullback U hS hs
  obtain ⟨z₂, hz₂⟩ := shortExact_pullback U hP hj
  obtain ⟨flP, hP₁, -⟩ := Vert.Flag.concat_spec U.toScheme _ _ _ _ _ z₁ hz₁ m₁ a flS
    (flA.ofIso (PreservesCokernel.iso Φ s))
  obtain ⟨flE, hE₁, -⟩ := Vert.Flag.concat_spec U.toScheme _ _ _ _ _ z₂ hz₂ (m₁ + a) b flP
    (flB.ofIso (PreservesCokernel.iso Φ j))
  obtain ⟨c₁, hc₁⟩ := hP₁ ⟨m₁, by omega⟩ (Fin.last m₁) rfl
  obtain ⟨c₂, hc₂⟩ := hE₁ ⟨m₁, by omega⟩ ⟨m₁, by omega⟩ rfl
  obtain ⟨c₃, hc₃⟩ := hE₁ ⟨m₁ + a, by omega⟩ (Fin.last (m₁ + a)) rfl
  refine ⟨U, hxU, flE, (asIso (flS.ι (Fin.last m₁))).symm ≪≫ c₁.symm ≪≫ c₂.symm,
    (asIso (flP.ι (Fin.last (m₁ + a)))).symm ≪≫ c₃.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hc₂, Iso.inv_hom_id_assoc,
      hc₁, IsIso.inv_hom_id_assoc, Functor.map_comp]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hc₃, Iso.inv_hom_id_assoc,
      IsIso.inv_hom_id_assoc]

end GlobalTheory.FlagTwoSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLevelOfIsAlgClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem nonempty_level_of_isAlgClosed :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (K : Type) [Field K] [IsAlgClosed K],
    (N : K) ≠ 0 → ∀ X : Obj F 𝔠 (Sp K), Nonempty (X.Level N) :=
  nonempty_level_of_torsion_basis torsion_free_rank_two

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeLatticeMultiplier
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ConjApprox

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_mapsTo)

theorem exists_approx {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (n : ℕ) :
    ∃ m : K, m ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K := by
  set a : Af K := algebraMap K (Af K) (n : K)⁻¹
  set ti : Af K := ((t⁻¹ : (Af K)ˣ) : Af K)
  set U : Set (Af K) := {x | ∀ v : HeightOneSpectrum (𝓞 K), (a * (ti * x - 1)) v ∈ v.adicCompletionIntegers K}
  have hO : IsOpen {z : Af K | ∀ v : HeightOneSpectrum (𝓞 K), z v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have hU : IsOpen U :=
    hO.preimage (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const))
  have hV : IsOpen (U ∩ {0}ᶜ) := hU.inter isClosed_singleton.isOpen_compl
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (𝓞 K)
  let v0 : HeightOneSpectrum (𝓞 K) :=
    ⟨m0, hm0.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm0 (RingOfIntegers.not_isField K)⟩
  haveI : Nontrivial (Af K) := ⟨⟨0, 1, fun h => by
    have h' := congrArg (fun x : Af K => x v0) h
    exact zero_ne_one h'⟩⟩
  have ht : (t : Af K) ∈ U ∩ {0}ᶜ := by
    refine ⟨fun v => ?_, t.ne_zero⟩
    have : ti * (t : Af K) - 1 = 0 := by simp [ti]
    rw [this, mul_zero]
    exact zero_mem _
  obtain ⟨m, hm1, hm2⟩ := GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨_, ht⟩
  refine ⟨m, fun h => hm2 (by simp [h]), hm1⟩

theorem finiteAdeleMap_algebraMap {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (x : K) : finiteAdeleMap K E (algebraMap K (Af K) x) = algebraMap E (Af E) (algebraMap K E x) :=
  FiniteAdeleRing.ext _ fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe K E w x

theorem mem_of_approx {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ) (k j : ℕ) (hk : 0 < k) (hj : 0 < j) (hjc : ((j : ℕ) : OF E) ∈ c) (m : K)
    (hm : ∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) :
    ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) *
          ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro u hu
  set zK : Af K := algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)
    with hzK
  set Z : Af E := finiteAdeleMap K E zK with hZ
  have hZi : ∀ w : HeightOneSpectrum (𝓞 E), Z w ∈ w.adicCompletionIntegers E := fun w =>
    finiteCompletionMap_mapsTo K E w (hm (w.under (𝓞 K)))
  have hjZ : (j : Af E) * Z ∈ hatO c := by
    have := GlobalTheory.CMVal.PicFin.mul_mem_hatO hjc hZi
    simpa only [map_natCast] using this
  set U' : Af E := ((upIdele K E t : (Af E)ˣ) : Af E) with hU'
  set Ui : Af E := (((upIdele K E t)⁻¹ : (Af E)ˣ) : Af E) with hUi
  set Yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E) with hYi
  set M : Af E := algebraMap E (Af E) (algebraMap K E m) with hM
  set Uu : Af E := algebraMap E (Af E) u with hUu
  set Kinv : Af E := algebraMap E (Af E) (k : E)⁻¹ with hKinv
  have e1 : U' * Ui = 1 := Units.mul_inv _
  have e3 : (k : Af E) * Kinv = 1 := by
    rw [hKinv, ← map_natCast (algebraMap E (Af E)), ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
  have eK : ((k * j : ℕ) : Af K) * algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap K (Af K)), ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hk hj).ne'), map_one]
  have e2K : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m = 1 + ((k * j : ℕ) : Af K) * zK := by
    rw [hzK]; linear_combination (-(((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) * eK
  have e2 : Ui * M = 1 + (k : Af E) * ((j : Af E) * Z) := by
    have := congrArg (finiteAdeleMap K E) e2K
    rw [map_mul, map_add, map_one, map_mul, map_natCast, finiteAdeleMap_algebraMap] at this
    have hUi' : Ui = finiteAdeleMap K E ((t⁻¹ : (Af K)ˣ) : Af K) := by rw [hUi, ← map_inv]; rfl
    rw [hUi', hM, this, hZ]
    push_cast
    ring
  have hA : Ui * M ∈ hatO c := by
    rw [e2]
    refine add_mem (one_mem _) (mul_mem ?_ hjZ)
    exact_mod_cast natCast_mem (hatO c) k
  have hu' : Uu * U' * Yi ∈ hatO c := by
    have h := hu
    simp only [lattice, Set.mem_setOf_eq, mul_inv_rev, inv_inv, Units.val_mul] at h
    rw [hUu, hU', hYi, _root_.mul_assoc]; exact h
  constructor
  · show algebraMap E (Af E) (algebraMap K E m * u) * Yi ∈ hatO c
    have : algebraMap E (Af E) (algebraMap K E m * u) * Yi = (Ui * M) * (Uu * U' * Yi) := by
      rw [map_mul]; linear_combination (-(M * Uu * Yi)) * e1
    rw [this]; exact mul_mem hA hu'
  · have : (U' * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * Yi =
        -((j : Af E) * Z) * (Uu * U' * Yi) := by
      simp only [div_eq_mul_inv, map_mul]
      rw [← hKinv, ← hM, ← hUu]
      linear_combination (Kinv * Uu * Yi * M) * e1 - (Kinv * Uu * Yi * U') * e2 - ((j : Af E) * Z * Uu * U' * Yi) * e3
    rw [this]; exact mul_mem (neg_mem hjZ) hu'

theorem approx_idele : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ k : ℕ, 0 < k → ∃ (m : K) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ Complex.normSq (io m) = b / modF t ∧
      ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ t c y hc k hk
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero (by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff])
  have hNc : ((N : ℕ) : OF E) ∈ c := Ideal.absNorm_mem c
  obtain ⟨m, hm0, hm⟩ := exists_approx t (k * N)
  obtain ⟨b, hb0, hbk, hb⟩ := GlobalTheory.T.norm_coprime_idele_approximation t k (k * N) (Nat.mul_pos hk hN) (dvd_mul_right k N) m hm0 hm
  exact ⟨m, b, hb0, hbk, by rw [GlobalTheory.T.norm_sq_embedding_imag_quadratic d δ io hK hd hδ, hb], mem_of_approx t c y k N hk hN hNc m hm⟩

end GlobalTheory.ConjApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCokerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_eq_inv_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ), Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  first | (exact @GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker) | (exact GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker) | (intros; apply GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullback
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

namespace GlobalTheory.FlagCls

theorem isNormalScheme_of_isPreimmersion_of_flat {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isNormalScheme_of_isPullback_fractionField : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N G : Scheme.{0}) (g : N ⟶ Sp R) (j : G ⟶ N) (s : G ⟶ Sp K), IsPullback j s g (spMap (algebraMap R K)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G := by
  intro R K _ _ _ _ _ N G g j s hp hN
  have hb : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) hp.flip hb
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) hp.flip hbf
  exact isNormalScheme_of_isPreimmersion_of_flat j hN

end GlobalTheory.FlagCls
end

