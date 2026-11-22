import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
namespace GlobalTheory.BoxLine

theorem exists_isPullback_pow {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) (A B : Over S')
    (φ₀ : A.left ⟶ G.left) (h : IsPullback φ₀ A.hom G.hom g) (N : ℕ) (q : Fin N → (B ⟶ A))
    (hl : IsLimit (Fan.mk B q)) :
    ∃ φ : B.left ⟶ (pow G N).left, IsPullback φ B.hom (pow G N).hom g ∧
      ∀ k, φ ≫ pr G N k = (q k).left ≫ φ₀ := by
  let ψ : Over.mk (B.hom ≫ g) ⟶ pow G N := Pi.lift fun k =>
    Over.homMk ((q k).left ≫ φ₀) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.w, ← Category.assoc, Over.w])
  have hψ : ∀ k, ψ.left ≫ pr G N k = (q k).left ≫ φ₀ := fun k => by
    have : ψ ≫ Pi.π (fun _ => G) k = _ := Pi.lift_π _ k
    exact congrArg (fun t => Over.Hom.left t) this
  have hw : ψ.left ≫ (pow G N).hom = B.hom ≫ g := Over.w ψ
  have hpr : ∀ k, pr G N k ≫ G.hom = (pow G N).hom := fun k => Over.w (Pi.π (fun _ => G) k)
  refine ⟨ψ.left, ⟨⟨hw⟩, ⟨?_⟩⟩, hψ⟩
  let c : ∀ s : PullbackCone (pow G N).hom g, Fin N → (Over.mk s.snd ⟶ A) := fun s k =>
    Over.homMk (h.lift (s.fst ≫ pr G N k) s.snd (by rw [Category.assoc, hpr, s.condition]))
      (h.lift_snd _ _ _)
  have hc : ∀ s k, (c s k).left ≫ φ₀ = s.fst ≫ pr G N k := fun s k => h.lift_fst _ _ _
  let m : ∀ s : PullbackCone (pow G N).hom g, Over.mk s.snd ⟶ B := fun s =>
    hl.lift (Fan.mk _ (c s))
  have hm : ∀ s k, (m s).left ≫ (q k).left = (c s k).left := fun s k =>
    congrArg (fun t => Over.Hom.left t) (hl.fac (Fan.mk _ (c s)) ⟨k⟩)
  refine PullbackCone.IsLimit.mk _ (fun s => (m s).left) ?_ ?_ ?_
  · intro s
    have hs : (m s).left ≫ B.hom = s.snd := Over.w (m s)
    let u : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk ((m s).left ≫ ψ.left) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hw, ← Category.assoc, hs])
    let v : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk s.fst s.condition
    have huv : u = v := by
      refine Pi.hom_ext _ _ fun k => ?_
      ext1
      change ((m s).left ≫ ψ.left) ≫ pr G N k = s.fst ≫ pr G N k
      rw [Category.assoc, hψ, ← Category.assoc, hm, hc]
    exact congrArg (fun t => Over.Hom.left t) huv
  · intro s
    exact Over.w (m s)
  · intro s t h1 h2
    let u : Over.mk s.snd ⟶ B := Over.homMk t h2
    have : u = m s := by
      refine hl.uniq (Fan.mk _ (c s)) u ?_
      rintro ⟨k⟩
      ext1
      change t ≫ (q k).left = (c s k).left
      refine h.hom_ext ?_ ?_
      · rw [hc, Category.assoc, ← hψ, ← Category.assoc, h1]
      · rw [Category.assoc, Over.w, h2]
        exact (Over.w (c s k)).symm
    exact congrArg (fun t => Over.Hom.left t) this

open GlobalTheory.CechPic in

theorem cls_pull_box {S : Scheme.{0}} (G : Over S) (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {X : Scheme.{0}} (φ : X ⟶ (pow G N).left) (h : ((boxLB G L N).pull φ).IsLB) :
    cls ((boxLB G L N).pull φ) h = ∑ k, pull (φ ≫ pr G N k) (cls L hL) := by
  rw [cls_pull (LB.isLB_linComb hL _ _), cls_linComb hL, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_smul, pull_comp]

theorem isLB_triv (X : Scheme.{0}) : (LB.triv X).IsLB :=
  ⟨by simp, fun _ => map_one _, fun _ _ _ => by simp⟩

open GlobalTheory.CechPic in

theorem sections_line : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  intro V K _ _ f G _ _ L rig θ n w x hL hx N
  obtain ⟨φ₀, he, e, hg, F, hpb, hegen, -⟩ := hx
  have hbox : ∀ {X : Scheme.{0}} (φ : X ⟶ (pow G N).left), ((boxLB G L N).pull φ).IsLB :=
    fun φ => LB.isLB_linComb (LB.isLB_linComb hL _ _) _ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨φ, hφ, -⟩ := exists_isPullback_pow (spMap f) G x.P.A (Over.mk (𝟙 (Sp K))) φ₀ hpb.1 0
      (fun k => k.elim0)
      (Fan.IsLimit.mk _ (fun s => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
        (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _))
    refine ⟨Sp K, 𝟙 _, φ, LB.triv _, ⟨fun _ => 1, fun _ _ => by simp⟩, hφ, isLB_triv _, ?_, ?_⟩
    · rw [iso_triv_iff, ← cls_eq_zero_iff (hbox φ), cls_pull_box G L hL]
      simp
    · intro s
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (s.f PUnit.unit), fun i => ?_⟩
      obtain rfl : i = PUnit.unit := rfl
      have h0 : ∀ (h : (⊤ : (Sp K).Opens) ≤ ⊤) (t : Γ(Sp K, ⊤)),
          ((Sp K).presheaf.map (homOfLE h).op).hom t = t := fun h t => by
        rw [show homOfLE h = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
        rfl
      simp [constFn, Scheme.Hom.appLE]
      exact (h0 _ _).symm
  · obtain ⟨y, p, -⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x N hN
    obtain ⟨φ, hφ, hc⟩ := exists_isPullback_pow (spMap f) G x.P.A y.P.A φ₀ hpb.1 N p.pr p.lim
    obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section GlobalTheory.firstFiveLaws.2.1.secTwist y.P
    refine ⟨y.P.A.left, y.P.A.hom, φ, y.P.L, b, hφ, y.P.isLB, ?_, fun s => (hb s).exists⟩
    have h1 : cls x.P.L x.P.isLB = pull φ₀ (cls L hL) := by
      rw [← cls_pull hL φ₀ (LB.isLB_linComb hL _ _), cls_eq_iff]
      exact ⟨e, hegen⟩
    have h2 : cls y.P.L y.P.isLB
        = cls (Out.boxLB x.P.L p.pr) (LB.isLB_linComb x.P.isLB _ _) := by
      rw [cls_eq_iff]
      exact ⟨p.w, p.w_gen⟩
    rw [← cls_eq_iff y.P.isLB (hbox φ), cls_pull_box G L hL, h2, cls_linComb x.P.isLB]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_smul, hc, pull_comp, h1]

end GlobalTheory.BoxLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelTangentOfPullbackTangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanPull

theorem one_left_congr {X Z : Scheme.{0}} {G : Over X} [GrpObj G] {f g : Z ⟶ X} (h : f = g) :
    (1 : Over.mk f ⟶ G).left = (1 : Over.mk g ⟶ G).left := by
  subst h; rfl

theorem isTanAtG_comp
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) : IsTanAtG Y.t x (w.left ≫ ψ.φ) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, ψ.cart.1.w, ← Category.assoc, Over.w w]
    rfl
  · rw [← Category.assoc, hw]
    refine (Formalism.L2.Pj.grpPull_one ψ.cart (ptOver V V)).symm.trans (one_left_congr ?_)
    show spMap (algebraMap V V) ≫ x = x
    have : spMap (algebraMap V V) = 𝟙 _ := by
      rw [Algebra.algebraMap_self]; exact Spec.map_id _
    rw [this, Category.id_comp]

theorem exists_tanM_of_isTan
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) :
    ∃ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (Formalism.L2.Pj.ovT (isTanAtG_comp x G ψ w hw)) (Formalism.L2.Pj.smT_zero_ovT _), rfl⟩

end GlobalTheory.TanPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeatPrimeLevelAutSubgroupUnipotent
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

namespace GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters Formalism.L2.Pj

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_plOver (j : Fin 2) : Nonempty (PlOver D.host j) := by
  have hne : Ideal.span {((D.host.g j : ℕ) : 𝓞 D.host.F)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have : ((D.host.g j : ℕ) : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) (D.host.g j : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank] at h1
    have hd : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
    have hg := (D.host.g_prime j).two_le
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have : 2 ^ Module.finrank ℚ D.host.F ≤ D.host.g j ^ Module.finrank ℚ D.host.F := Nat.pow_le_pow_left hg _
    have : 2 ≤ 2 ^ Module.finrank ℚ D.host.F := Nat.le_self_pow hd.ne' 2
    omega
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hg : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨⟨P, hP.isPrime, fun e => ?_⟩, hg⟩⟩
  rw [e, Ideal.mem_bot] at hg
  exact (D.host.g_prime j).ne_zero (by exact_mod_cast hg)

theorem isNilpotent_sub_one_of_unitri {r : ℕ} {k : Type} [Field k] {u : GL (Fin r) k} (hu : u ∈ unitri r k) :
    IsNilpotent ((u : Matrix (Fin r) (Fin r) k) - 1) := by
  have ht : ((u : Matrix (Fin r) (Fin r) k) - 1).BlockTriangular id := hu.1.sub Matrix.blockTriangular_one
  have hc : ((u : Matrix (Fin r) (Fin r) k) - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular _ ht]
    simp [hu.2]
  refine ⟨r, ?_⟩
  have := Matrix.aeval_self_charpoly ((u : Matrix (Fin r) (Fin r) k) - 1)
  rwa [hc, map_pow, Polynomial.aeval_X] at this

theorem neat_typePrime (hM : D.host.g 0 * D.host.g 1 ∣ l.M) (hg : ∀ k, Dw.p + Dw.q + 1 < D.host.g k)
    (v : Sq D.host) : NeatPrime (typePrime l v) (D.host.g v.1) (Dw.p + Dw.q) ∧ (typePrime l v).IsPrime := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd (D := D) v.1).trans hM
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  refine ⟨⟨D.host.g_prime v.1, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v),
    fun hmem => ?_, hg v.1⟩, hP⟩
  have h0 : Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime v.1).ne_zero
  have hsq : Squarefree (Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)}) :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D v.1).2
  have hd : typePrime l v * typePrime l v ∣ Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]
    exact hmem
  exact hP.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))

theorem unipAt_of_unitri (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host)
    (hγ : typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1))) : UnipAt (typePrime l v) γ := by
  obtain ⟨n, hn⟩ := isNilpotent_sub_one_of_unitri hγ
  set Nm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)) :=
    ((typeRed fr γ v : GL (Fin D.R.r) (ZMod (D.host.g v.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) - 1
    with hNm
  let π : Dw.La →ₗ[𝓞 D.host.E] QMod Dw.La (typePrime l v) := Submodule.mkQ _
  have key : ∀ (m : ℕ) (x : Dw.La), fr v (π (((liftLa γ - 1) ^ m) x)) = (Nm ^ m).mulVec (fr v (π x)) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      generalize ((liftLa γ - 1) ^ m) x = y
      have h1 : π (liftLa γ y) = qProj (J := typePrime l v) le_sup_left
          (γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y)) := by
        rw [← liftLa_spec]; rfl
      have h2 : π y = qProj (J := typePrime l v) le_sup_left ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y) := rfl
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, h1, h2, hNm, Matrix.sub_mulVec,
        Matrix.one_mulVec, typeRed_mulVec]
  refine ⟨n, fun x => ?_⟩
  have h := key n x
  rw [hn, Matrix.zero_mulVec, AddEquivClass.map_eq_zero_iff] at h
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem exists_index (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)) (hS : S = grpHR fr ∨ ∃ k, S = grpGHR fr k) :
    ∃ j : Fin 2, ∀ γ ∈ S, ∀ v : Sq D.host, v.1 = j → typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1)) := by
  rcases hS with rfl | ⟨k, rfl⟩
  · exact ⟨0, fun γ hγ v _ => hγ v trivial⟩
  · refine ⟨k + 1, fun γ hγ v hv => hγ v ?_⟩
    show v.1 ≠ k
    rw [hv]; fin_cases k <;> decide

end GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.OrbitSep.UnipPrime GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters in

theorem GlobalTheory.OrbitSep.exists_neatPrime_unipAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  intro D H Dw l hM hg fr S hS
  obtain ⟨j, hj⟩ := exists_index fr S hS
  obtain ⟨w⟩ := exists_plOver (D := D) j
  let v : Sq D.host := ⟨j, w⟩
  obtain ⟨hN, -⟩ := neat_typePrime (Dw := Dw) hM hg v
  exact ⟨typePrime l v, D.host.g v.1, hN, le_sup_left, fun γ hγ => unipAt_of_unitri fr γ v (hj γ hγ v rfl)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspSectionLargeEvenScalarWeight
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

theorem GlobalTheory.ScalarPoin.exists_cusp_ne_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ N
  obtain ⟨y, hy⟩ := GlobalTheory.FlagSecProbe.dom_nonempty X
  obtain ⟨n, hN, -, hev, P, hP, hPy⟩ := GlobalTheory.ScalarPoin.exists_cusp_ne E r X hp0 hpr hχ y hy N
  exact ⟨n, hN, hev, P, hP, y, hy, hPy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroTraceElement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

open Polynomial

theorem intCasimir_exists : ∀ (E : Type) [Field E] [NumberField E], ∃ (d : ℕ) (c θ : Fin d → 𝓞 E),
    (∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j) ∧ ∑ j, c j * θ j ≠ 0 := by
  intro E _ _
  classical
  obtain ⟨α, -, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := ℂ) (RingHom.id ℂ)
    (fun τ => τ.comp (algebraMap (𝓞 E) E)) (fun _ _ => rfl)
  let g : ℤ[X] := minpoly ℤ α
  have hgα : aeval α g = 0 := minpoly.aeval ℤ α
  have hroot : (g.map (algebraMap ℤ (𝓞 E))).IsRoot α := by
    rw [IsRoot, Polynomial.eval_map, ← aeval_def, hgα]
  let q := (g.map (algebraMap ℤ (𝓞 E))) /ₘ (X - C α)
  have hq : (X - C α) * q = g.map (algebraMap ℤ (𝓞 E)) := mul_divByMonic_eq_iff_isRoot.2 hroot
  let iL : 𝓞 E →+* 𝓞 E ⊗[ℤ] 𝓞 E := Algebra.TensorProduct.includeLeftRingHom
  let iR : 𝓞 E →+* 𝓞 E ⊗[ℤ] 𝓞 E := (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] _).toRingHom
  have hiL : ∀ x, iL x = x ⊗ₜ[ℤ] 1 := fun _ => rfl
  have hiR : ∀ x, iR x = 1 ⊗ₜ[ℤ] x := fun _ => rfl
  let T : 𝓞 E ⊗[ℤ] 𝓞 E := q.eval₂ iL (iR α)
  have hT : T = ∑ j : Fin (q.natDegree + 1), q.coeff j ⊗ₜ[ℤ] (α ^ (j : ℕ)) := by
    show q.eval₂ iL (iR α) = _
    rw [eval₂_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => iL (q.coeff n) * (iR α) ^ n)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hiL, hiR, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.mul_one, _root_.one_mul]
  have hαT : iR α * T = iL α * T := by
    have h1 : ((X - C α) * q).eval₂ iL (iR α) = 0 := by
      rw [hq, eval₂_map]
      have : iL.comp (algebraMap ℤ (𝓞 E)) = iR.comp (algebraMap ℤ (𝓞 E)) := RingHom.ext_int _ _
      rw [this, ← hom_eval₂, ← aeval_def, hgα, map_zero]
    rw [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at h1
    exact sub_eq_zero.1 (by rw [← sub_mul]; exact h1)
  let I : Ideal (𝓞 E ⊗[ℤ] 𝓞 E) := (Submodule.span (𝓞 E ⊗[ℤ] 𝓞 E) {T}).annihilator
  have hmemI : ∀ r, r ∈ I ↔ r * T = 0 := fun r => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  let π := Ideal.Quotient.mk I
  have hπα : (π.comp iR).toIntAlgHom α = (π.comp iL).toIntAlgHom α := by
    show π (iR α) = π (iL α)
    rw [Ideal.Quotient.eq, hmemI, sub_mul, hαT, sub_self]
  have key : ∀ p : ℤ[X], π (iR (aeval α p)) = π (iL (aeval α p)) := fun p => by
    have h1 := aeval_algHom_apply (π.comp iR).toIntAlgHom α p
    have h2 := aeval_algHom_apply (π.comp iL).toIntAlgHom α p
    rw [hπα] at h1
    exact h1.symm.trans h2
  haveI : Module.Free ℤ (𝓞 E) := inferInstance
  haveI : Module.Free ℤ (𝓞 E ⊗[ℤ] 𝓞 E) := Module.Free.of_basis
    ((Module.Free.chooseBasis ℤ (𝓞 E)).tensorProduct (Module.Free.chooseBasis ℤ (𝓞 E)))
  haveI : Module.IsTorsionFree ℤ (𝓞 E ⊗[ℤ] 𝓞 E) := inferInstance
  have hall : ∀ o : 𝓞 E, iR o * T = iL o * T := by
    intro o
    obtain ⟨N, p, hN0, hNp⟩ := hN o
    have h := key p
    rw [← hNp, Ideal.Quotient.eq, hmemI, map_mul, map_mul, map_intCast, map_intCast, ← mul_sub,
      _root_.mul_assoc, ← zsmul_eq_mul] at h
    rw [← sub_eq_zero, ← sub_mul]
    exact (smul_eq_zero.1 h).resolve_left hN0
  refine ⟨q.natDegree + 1, fun j => q.coeff j, fun j => α ^ (j : ℕ), fun o => ?_, ?_⟩
  · have h := hall o
    rw [hT, Finset.mul_sum, Finset.mul_sum] at h
    convert h using 2 with j
    · rw [hiR, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    · rw [hiL, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
  · have hsum : ∑ j : Fin (q.natDegree + 1), q.coeff j * α ^ (j : ℕ) = q.eval α := by
      rw [eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => q.coeff n * α ^ n)]
    rw [hsum]
    have hd := congrArg derivative hq
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, _root_.one_mul,
      derivative_map] at hd
    have he := congrArg (eval α) hd
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_map,
      ← aeval_def] at he
    rw [he]
    intro h0
    have hE : aeval (α : E) (derivative g) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, h0, map_zero]
    have hint : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
    have hmin : minpoly ℚ (α : E) = g.map (algebraMap ℤ ℚ) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, NumberField.RingOfIntegers.minpoly_coe]
    have hsep := (Algebra.IsSeparable.isSeparable ℚ (α : E)).aeval_derivative_ne_zero
      (minpoly.aeval ℚ (α : E))
    rw [hmin, derivative_map, aeval_map_algebraMap] at hsep
    exact hsep hE

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightDecompositionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parallel_weight_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), GapGe 1 la → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  first | exact @GlobalTheory.WtMatchArith.exists_dom_exponents | exact GlobalTheory.WtMatchArith.exists_dom_exponents | (intros; apply GlobalTheory.WtMatchArith.exists_dom_exponents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltrationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarization_form_isotropic_filtration : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧ ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  first | exact @GlobalTheory.PolExistsRing.polForm_exists | exact GlobalTheory.PolExistsRing.polForm_exists | (intros; apply GlobalTheory.PolExistsRing.polForm_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerXStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∀ (k : A →+* ℂ), Function.Injective k → ∀ (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (ι : S →+* ℂ⸨X⸩), (∀ s : PowerSeries A, ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s)) → ∀ v : S, ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range → (∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s) → ∃ s : PowerSeries A, v = algebraMap _ S s := by
  first | exact @GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | exact GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | (intros; apply GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.LargeAll

set_option maxHeartbeats 800000 in

theorem exists_smul_nonneg_large : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  intro _ D T j Y e o hY _ a n hdom hn f hf
  obtain ⟨s, hs, h⟩ := GlobalTheory.LargeCover.exists_smul_nonneg_all D T j Y e o hY a n hdom hn f hf
  have hsm : (algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s) • f = s • f :=
    @algebraMap_smul (𝓞 Y.d.c₂.F) _ Y.d.c₂.F _ _ (Rul Y.d.Xo₂ Y.d.c₂) _ _ _ (Formalism.L2.Pj.rulesTower _) s f
  refine ⟨algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s, by simpa using hs, fun la v hv => ?_⟩
  rw [hsm]
  exact h la v hv

end GlobalTheory.LargeAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGeneratedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sec_nonzero_on_finite_of_generated' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_nonzero_on_finite_of_generated | exact GlobalTheory.exists_sec_nonzero_on_finite_of_generated | (intros; apply GlobalTheory.exists_sec_nonzero_on_finite_of_generated <;> assumption)
end

