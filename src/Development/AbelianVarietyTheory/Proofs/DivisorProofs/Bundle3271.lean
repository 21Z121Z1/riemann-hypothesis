import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.ThIntAll

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem relDim_eq_of_sharp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {P : PolAV F.X}
    (hPg : P.g = 8 * g) (hPs : GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X)) {T : Scheme.{0}} [Nonempty T] (Q : PolAV T)
    (u : T ⟶ F.X) (hQ : GlobalTheory.Poinc.SharpOver F W Q u) : Q.g = 8 * g := by
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.sharp_polarization_unique_pullback g n F W Q P u (𝟙 F.X) u (Category.comp_id u) hQ hPs
  have h1 : SmoothOfRelativeDimension (8 * g) Q.A.hom := by
    rw [← hPg]; exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique Q.A.hom Q.smoothDim h1 ((η[Q.A]).left (Nonempty.some (inferInstanceAs (Nonempty T))))

theorem exists_symE_pCrd_of_sharp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {P : PolAV F.X}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {m N : ℕ} {f : F.X ⟶ PSpace (cycAway n) N} (hT : ThAt F W P rig m f)
    {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X) (hSg : S.g = 8 * g) (hρs : GlobalTheory.Poinc.SharpOver F W ρ.P u) :
    ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N),
      h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  obtain ⟨hPg, hPs, hrig, hm, -, hmu, hN, -, hf, -⟩ := hT
  haveI : CharZero Ω := hA.char
  have hSB : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  let v : S.R →+* Ω := S.R.val.toRingHom
  obtain ⟨P₀, φ, hg₀, hφ, hL₀⟩ := exists_isPolFibre polBaseChange_holds v ρ.P
  have hφ' : IsGrpPullback P₀.A ρ.P.A (spMap v ≫ 𝟙 (Sp S.R)) φ := by
    simpa using hφ
  have hL₀' : LBIso P₀.L (ρ.P.L.pull φ) := hL₀.symm
  have hfib : PolFib ρ.P.A ρ.P.L (8 * g) (spMap v ≫ 𝟙 (Sp S.R)) :=
    ⟨P₀, φ, by rw [hg₀, ρ.g_eq, hSg], hφ', hL₀'⟩
  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s =>
    (ρ.th₁_basis s).exists.elim fun r h => ⟨r 0, fun j => (h j).trans (Fin.sum_univ_one _)⟩
  let θ : SecAt ρ.P.A ρ.P.L (spMap v ≫ 𝟙 (Sp S.R)) := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap v ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.EmbPull.isGenSec_pullS ρ.P hSB _ hth
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) Ω
    (spMap v ≫ 𝟙 (Sp S.R)) θ hm hN hfib
  have hmΩ : (m : Ω) ≠ 0 := by
    let κ : cycAway n →+* S.R := (Spec.preimage (u ≫ F.s)).hom
    have := (hmu.map κ).map v
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  refine ⟨e, ⟨by rw [hSg]; exact hN, hmΩ, he⟩, fun h hh => ?_⟩
  obtain ⟨ψ, hψ, hLψ⟩ := GlobalTheory.T.sharp_polarization_unique_pullback g n F W ρ.P P u (𝟙 F.X) u (Category.comp_id u) hρs hPs
  have hα : IsGrpPullback P₀.A P.A ((spMap v ≫ u) ≫ 𝟙 F.X) (φ ≫ ψ) := by
    simpa using hφ.comp hψ
  have hLα : LBIso P₀.L (P.L.pull (φ ≫ ψ)) :=
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB φ) (pull_isLB P.isLB _) hL₀'
      (LBIso.trans (pull_isLB ρ.P.isLB φ) (pull_isLB (pull_isLB P.isLB ψ) φ) (pull_isLB P.isLB _)
        (RigidBundleGlue.LBIso.pull hLψ φ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp P.isLB ψ φ).symm)
  have key := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre F.X P.A P.L rig P.isLB hrig (8 * g) m N (cycAway n) F.X (𝟙 F.X) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig
    Ω (spMap v ≫ u) (spMap v ≫ 𝟙 (Sp S.R)) P₀ (φ ≫ ψ) φ θ e hm hN hf ρ.P.isLB ρ.rig_gen
    (by rw [hg₀, ρ.g_eq, hSg]) hα hLα hφ' hL₀' hθ he
  rw [hh, show algebraMap S.R Ω = v from RingHom.ext fun _ => rfl]
  simpa [Category.assoc] using key

theorem thetaInt_all : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → GlobalTheory.Poinc.ThetaInt F W f := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ S ρ u hρs _ M h hnorm hpt
  have hSg : S.g = 8 * g := by
    rw [← ρ.g_eq]; exact relDim_eq_of_sharp hTh.1 hTh.2.1 ρ.P u hρs
  obtain ⟨e, hSym, hCrd⟩ := exists_symE_pCrd_of_sharp hTh S ρ u hSg hρs
  have hCrd' : PCrd (M.pt ≫ h) e := by
    rw [hpt]; exact hCrd _ rfl
  have hDe : M.HasDiv e := GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o Ω (cycAway n) M N h e hCrd'
  obtain ⟨-, -, -, hm, hm3, hmu, hNm, -, -⟩ := hTh
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : CharZero Ω := ArithBase.char o
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  letI := ρ.P.isAb.comm
  obtain ⟨j, hj1, hr⟩ := ρ.r_eq
  have hnodd := ρ.n_odd
  have hnp := ρ.n_prime
  have hrNodd : Odd (S.r * S.N) := by
    rw [hr, ρ.N_eq]; exact hnodd.pow.mul hnodd.pow.pow
  have hrN3 : 3 ≤ S.r * S.N := by
    have hn3 : 3 ≤ ρ.n := by
      have := hnp.two_le
      rcases hnodd with ⟨k, hk⟩
      omega
    have h1 : ρ.n ≤ S.r := by rw [hr]; exact Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ S.N := by have := S.N_ge; omega
    nlinarith
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o Ω M S.Gam (Fin (N + 1)) S.th e (N + 1).factorial (Nat.factorial_pos _)
    ((GlobalTheory.isNormalScheme_iff_pred _).1 hnorm) hDe ?_
  intro V _ _ _ hV ξ emb hξ j₀ hj₀ hint
  haveI : IsDiscreteValuationRing V := ((GlobalTheory.LN.cDvr_iff V).1 hV).1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let val : S.R →+* Ω := S.R.val.toRingHom
  let i₀ : S.R →+* FractionRing V := emb.comp val
  let iK : S.R →+* K := io.comp i₀
  let i' : Ω →+* K := io.comp emb
  let σ : o →+* V := (Spec.preimage (ξ ≫ M.s)).hom
  let τ : cycAway n →+* V := (Spec.preimage (ξ ≫ h ≫ PSpace.str (cycAway n) N)).hom
  have hmV : IsUnit (m : V) := by
    rw [← map_natCast τ]; exact hmu.map τ
  have hrNV : IsUnit ((S.r * S.N : ℕ) : V) := by rw [← map_natCast σ]; exact S.unit.map σ
  have hmK : (m : K) ≠ 0 := by
    have := hmV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  have hrNK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := hrNV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap i₀
  obtain ⟨P', φ, gp, hL'⟩ := GlobalTheory.UPoinc.exists_pol_baseChange ρ.P y
  letI := P'.isAb.comm
  have hS' : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change _ _ ρ.P.A P'.A y φ ρ.P.L P'.L ρ.P.isLB P'.isLB gp hL' ρ.hypS
  have hPF0 : PolFib ρ.P.A ρ.P.L (8 * g) (𝟙 (Sp S.R)) :=
    ⟨ρ.P, 𝟙 _, by rw [ρ.g_eq, hSg], grpPullback_self _, GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB⟩
  have hPFK : PolFib ρ.P.A ρ.P.L (8 * g) (spMap iK ≫ 𝟙 (Sp S.R)) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) (8 * g) S.R (𝟙 _)).2 K iK hPF0
  let θK := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ iK
  obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) K
    (spMap iK ≫ 𝟙 (Sp S.R)) θK hm hmK hNm hPFK
  obtain ⟨pt', c', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) (S.r * S.N)
    ((S.r * S.N) ^ (4 * (8 * g))) K (spMap iK ≫ 𝟙 (Sp S.R)) θK hrNodd hrNK rfl hPFK
  have hgen := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o Ω S ρ K iK
  have hxy : spMap io ≫ y = spMap iK ≫ 𝟙 (Sp S.R) := by
    rw [Category.comp_id]; exact spMap_comp_ring i₀ io
  have h2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' := by
    rw [hxy]; exact ⟨θK, pt, pt', hgen, hc, hc'⟩
  obtain ⟨a, ha, hp1, hp2⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P' φ gp hL' hS' K io
    m (S.r * S.N) (N + 1) _ c c' hm hm3 hmV hrNodd hrN3 hrNV h2
  have hreal := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K iK _ pt' c' hc'
  have hlist : ∃ pt'' : Fin (N + 1) → (Over.mk (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R))) ⟶ ρ.P.A),
      ThList ρ.P.A ρ.P.L ρ.rig m (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R)))
        (SecAt.pull ρ.P.A ρ.P.L (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ val) i') pt'' c := by
    simp only [SecAt.pull]
    rw [pullS_comp ρ.P.A ρ.P.isLB]
    refine thList_congr ρ.th₁ ?_ (Over.homMk (spMap iK) rfl) _ ?_ hc
    · rw [Category.comp_id, Category.comp_id]; exact (spMap_comp_ring val i').symm
    · simp only [Over.comp_left, Over.homMk_left]; exact (spMap_comp_ring val i').symm
  obtain ⟨pt'', hpt''⟩ := hlist
  have hsym : ∀ j, io (emb (e j)) = symTup c j := fun j => by unfold SymE SymAt at hSym; exact hSym.2.2 K i' pt'' c hpt'' j
  have hj₀' : emb (e j₀) ≠ 0 := (map_ne_zero emb).2 hj₀
  have hint' : ∀ j, emb (e j) / emb (e j₀) ∈ Set.range (algebraMap V (FractionRing V)) := fun j => by
    rw [← map_div₀]; exact hint j
  obtain ⟨H1, b, hb, H2⟩ := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (N + 1) ((S.r * S.N) ^ (4 * (8 * g))) ((S.r * S.N) ^ 2) S.Gam c c' a
    (fun j => emb (e j)) (fun b => emb (S.th b)) ha (Nat.one_le_pow _ _ (by omega)) hp1 hp2 hsym hreal.1 hreal.2 j₀ hj₀'
    hint'
  refine ⟨fun b' => ?_, b, fun h0 => hb (by rw [h0, map_zero]), ?_⟩
  · rw [map_div₀, map_pow]; exact H1 b'
  · rw [map_div₀, map_pow]; exact H2

end GlobalTheory.SiegTh.ThIntAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCharTangentFamily
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.HtGen.genOver_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime], CharFam t ρ' q 2 → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (k : ℕ) (hk : k ≤ m), GenOver V (fun y => ((∏ l : Fin k, d y (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)) (fun v e y => -∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) q := by
  intro E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ q _ hC m u₀ f d hf k hk
  obtain ⟨N, c, hc, hh⟩ := hC
  have hch : ∀ x : V.X, ∃ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ)
      (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X, U)),
      x ∈ U ∧ IsTanBasis t (hU.fromSpec ≫ ρ') e ∧
      ∀ (β : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap β ≫ hU.fromSpec = y →
        ∀ j, DlogIs t q 2 (c j y) (fun i => spMap (dualMap β) ≫ e i) (fun i => β (h j i)) := by
    intro x
    obtain ⟨⟨U, hU⟩, g, e, hx, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t V.X ρ' x
    obtain ⟨h, hh'⟩ := hh U hU g e he
    exact ⟨U, hU, g, e, h, hx, he, hh'⟩
  choose U hU g e h hx he hd using hch
  choose s hs using fun x => GlobalTheory.T.flag_frame_cover_tangent_compat E H X t F Y V ρ' ρ hρ m u₀ f d hf (U x) (hU x) (g x) (e x) (he x) (Fin N) (h x) k hk
  let eqv := Fintype.equivFin (Fin k → Fin N)
  refine ⟨Fintype.card (Fin k → Fin N), U, fun x J => s x (eqv.symm J), hx, fun x J z hz => ?_,
    fun v ε y z yt hq hzy hyt x hxU => ?_⟩
  · obtain ⟨α, a, -, -, hv⟩ := hs x z hz
    exact ⟨_, (hv _).symm⟩
  · obtain ⟨hp, -, -⟩ := ioOf_spec F v ε
    haveI := Fact.mk hp
    have P := fun x' (hx' : ⊤ ≤ yt ⁻¹ᵁ U x') => GlobalTheory.T.flag_frame_prime_tangent_compat E H X t hX F Y V ρ' ρ hρ q m f d hf.tan
      (fun y K _ ψ => hf.indep y K ψ) k hk N c hc (U x) (U x') (hU x) (hU x') (g x) (g x') (e x) (e x') (h x) (h x')
      (he x) (he x') (hd x) (hd x') (s x) (s x') (hs x) (hs x') v ε y z yt hq hzy hyt hxU hx'
    obtain ⟨hpos, hle, ⟨σ, heq⟩, -⟩ := P x hxU
    have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl fun l _ =>
      GlobalTheory.LineNorm.Chart.stepLog_eq ρ f q (Fin.castLE hk l) v ε y hp _ rfl
    have C := GlobalTheory.T.local_unit_absolute_value_criterion F v ε k _ hpos
    dsimp only
    rw [hsum]
    refine ⟨fun J => (C _).1.2 (hle _), ⟨eqv σ, ?_⟩, fun x' hx' J => (C _).2.2.2 ((P x' hx').2.2.2 _)⟩
    rw [Equiv.symm_apply_apply]
    exact (C _).2.1.2 heq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmPeriodsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_cm_periods : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∃ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  first | exact @GlobalTheory.ConjCMPoint.conjUnif_of_torsTransport | exact GlobalTheory.ConjCMPoint.conjUnif_of_torsTransport | (intros; apply GlobalTheory.ConjCMPoint.conjUnif_of_torsTransport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialStrictHenselisationOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_trivial_strict_henselisation_origin : GlobalTheory.LocAcyc.KeyOrigin := by
  first | (exact @GlobalTheory.KeyOriginCut.keyOrigin) | (exact GlobalTheory.KeyOriginCut.keyOrigin) | (intros; apply GlobalTheory.KeyOriginCut.keyOrigin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeries
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.OneMapExact.splitOff_of_dvd {D : D7} {V : HSp D} {b b' : ℕ} (hd : b ∣ b') {g : GA D V} (H : SplitOffBad V b' g) :
    SplitOffBad V b g := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hP hb => h3 PP hP ?_, h4⟩
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hb

theorem GlobalTheory.OneMapExact.trace_of_terms {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (S : GA D (Wc D i) → ℂ) (c : D.what₂.LL) (X : U → Fin (R.nW i) → D.what₂.LL)
    (w : ∀ τ, (R.MW i (sg0 D A)).sm τ)
    (H : ∀ u : U, adForm R i (X u) w =
      D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) S) :
    adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • X u) w = D.what₂.embLL c • levelTrace R i U ψ S := by
  classical
  have h0 : adForm R i 0 = 0 := by
    have := adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at this
    exact this
  have hadd : ∀ (s : Finset U) (Y : U → Fin (R.nW i) → D.what₂.LL),
      adForm R i (∑ u ∈ s, Y u) = ∑ u ∈ s, adForm R i (Y u) := by
    intro s Y
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adForm_add, ih]
  rw [finsum_eq_sum_of_fintype, hadd]
  simp only [adForm_smul]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  ext1 g
  simp only [MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.smul_apply,
    H, smul_eq_mul]
  set Fn : G → ℂ := fun d => (if hg : d ∈ U then D.what₂.embLL ((ψ ⟨d, hg⟩)⁻¹ : D.what₂.LLˣ) else 0) *
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG d) S g with hFn
  have e1 : ∑ d : G, Fn d = ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g := by
    calc ∑ d : G, Fn d = ∑ d ∈ Finset.univ.filter (· ∈ U), Fn d :=
          (Finset.sum_filter_of_ne fun d _ h => by
            by_contra hd
            exact h (by simp only [hFn, dif_neg hd, zero_mul])).symm
      _ = ∑ u : U, Fn u := Finset.sum_subtype _ (by simp) Fn
      _ = _ := Finset.sum_congr rfl fun u _ => by simp only [hFn, dif_pos u.2]
  have e2 : ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g =
      ∑ u : U, D.what₂.embLL ((ψ u⁻¹)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u⁻¹ : U) : G)) S g :=
    (Equiv.sum_comp (Equiv.inv U) (fun u : U => D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g)).symm
  rw [e2] at e1
  calc _ = D.what₂.embLL c * ∑ d : G, Fn d := by
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [map_inv, inv_inv, Subgroup.coe_inv]
        ring
    _ = _ := by
        congr 1

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.OneMapExact.one_term : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := GlobalTheory.T.shortSeries_trace_term_at_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w u =>
    GlobalTheory.T.lowestTypeEquality_of_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U χ ξR ω φ h17 Λ h (GlobalTheory.OneMapExact.splitOff_of_dvd (dvd_mul_right _ _) h18) h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27 y₀ c hr φ' hφ' u (fun w₀ hw₀ => H φ' hφ' w₀ hw₀ u) w⟩

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.OneMapExact.trace_short_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • levelTrace R i U ψ (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU ψ χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := GlobalTheory.OneMapExact.one_term D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w => GlobalTheory.OneMapExact.trace_of_terms R i U ψ _ c _ _ (H φ' hφ' w)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_torsion_point_map_commutes_char_injective_hom : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (A₁ A₂ : PolAV (Sp (FractionRing V))) (G₁ G₂ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  first | exact @GlobalTheory.Mum.Two.KeyDvr.main | exact GlobalTheory.Mum.Two.KeyDvr.main | (intros; apply GlobalTheory.Mum.Two.KeyDvr.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatchStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgression_term_density_good_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch | exact GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch | (intros; apply GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem linEnd_adjoint_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE g g' hg hg'
  obtain ⟨g₁, hg₁, hiso⟩ := GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group R hR D A G hG U g hg.1
  have h₁ : LinEnd U.toUnifPre a' h g₁ := GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint R hR D A G hG U a a' h h' hE g g₁ hg hg₁ hiso
  have hu := GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData R hR.1 D A G hG U a' h
  have heq : g₁ = g' := hu.2 g₁ g' fun e => congrFun (hu.1 _ _ h₁.2 hg'.2) e
  subst heq
  exact hiso

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_eighth_power_exists : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  first | exact @GlobalTheory.PowE8.exists_unif_pow8 | exact GlobalTheory.PowE8.exists_unif_pow8 | (intros; apply GlobalTheory.PowE8.exists_unif_pow8 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagBundleExistsStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_flag_bundle_exists : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ Sp ℤ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a))) r fl := by
  first | exact @GlobalTheory.FlagFree.exists_isFlagBundle_freeModule | exact GlobalTheory.FlagFree.exists_isFlagBundle_freeModule | (intros; apply GlobalTheory.FlagFree.exists_isFlagBundle_freeModule <;> assumption)
end

