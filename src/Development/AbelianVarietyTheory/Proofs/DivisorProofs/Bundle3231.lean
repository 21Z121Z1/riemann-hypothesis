import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionLocallyCutOutByIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

section Transport

variable {O T V W : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]
  (ψ : O →+* Module.End T V) (ν : O →+* Module.End T W) (e : V ≃ₗ[T] W) (he : ∀ c v, e (ψ c v) = ν c (e v))
include he

theorem mem_eigSub_transport (τ : O →+* T) (v : V) : e v ∈ eigSub ν τ ↔ v ∈ eigSub ψ τ := by
  simp only [mem_eigSub]
  refine forall_congr' fun c => ?_
  rw [← he, ← map_smul, e.injective.eq_iff]

theorem eigSub_transport (τ : O →+* T) : (eigSub ψ τ).map (e : V →ₗ[T] W) = eigSub ν τ := by
  ext w
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, ← mem_eigSub_transport ψ ν e he]
  simp

theorem finrank_eigSub_transport (τ : O →+* T) :
    Module.finrank T (eigSub ψ τ) = Module.finrank T (eigSub ν τ) := by
  rw [← eigSub_transport ψ ν e he τ]
  exact (e.submoduleMap (eigSub ψ τ)).finrank_eq

theorem lieMod_transport (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) :
    LieMod ψ ω ρ τ ↔ LieMod ν ω ρ τ := by
  constructor
  · intro h w hw
    obtain ⟨u, hu, hs⟩ := h (e.symm w) (by
      apply e.injective
      rw [he, map_smul, LinearEquiv.apply_symm_apply, hw])
    refine ⟨fun i => e (u i), fun i => (mem_eigSub_transport ψ ν e he _ _).2 (hu i), ?_⟩
    rw [← map_sum, ← hs, LinearEquiv.apply_symm_apply]
  · intro h v hv
    obtain ⟨u, hu, hs⟩ := h (e v) (by rw [← he, hv, map_smul])
    refine ⟨fun i => e.symm (u i), fun i => ?_, ?_⟩
    · rw [← mem_eigSub_transport ψ ν e he, LinearEquiv.apply_symm_apply]
      exact hu i
    · apply e.injective
      rw [map_sum, hs]
      simp

end Transport

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_baseMap {R : Type} [CommRing R] {S : Scheme.{0}} (s : S ⟶ Sp R) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ βB : R →+* Γ(S, U), ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'),
      spMap f ≫ hU.fromSpec ≫ s = spMap β → β = f.comp βB := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, fun R' _ f β h => ?_⟩
  have h2 : spMap (f.comp (Spec.preimage (hU.fromSpec ≫ s)).hom) = spMap β := by
    rw [← h, ← spMap_comp_spMap']
    congr 1
    show Spec.map (CommRingCat.ofHom (Spec.preimage (hU.fromSpec ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h3 := Spec.map_injective h2
  exact (congrArg CommRingCat.Hom.hom h3).symm

theorem lieHer_iff_mat {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {S : Scheme.{0}}
    {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {U : S.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) Γ(S, U))
    (hM : ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
      ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
        ∀ (c : 𝓞 D.F) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
          e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') (act.toF D) c v) = matAct M f c (e v))
    {R' : Type} [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R') :
    LieHer b act β (spMap f ≫ hU.fromSpec) ↔ LieHerMat b M f β := by
  unfold LieHer LieHerMat LieRankAt
  refine forall_congr' fun T' => forall_congr' fun _ => forall_congr' fun g => ?_
  have hx : spMap g ≫ spMap f ≫ hU.fromSpec = spMap (g.comp f) ≫ hU.fromSpec := by
    rw [← Category.assoc, spMap_comp_spMap']
  rw [hx]
  obtain ⟨e, he⟩ := hM T' (g.comp f)
  refine and_congr ?_ ?_
  · rw [GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition]
    exact lieMod_transport _ _ e he _ _ _
  · refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h =>
      forall_congr' fun i => ?_
    have hx2 : spMap h ≫ spMap (g.comp f) ≫ hU.fromSpec = spMap (h.comp (g.comp f)) ≫ hU.fromSpec := by
      rw [← Category.assoc, spMap_comp_spMap']
    rw [hx2]
    obtain ⟨e2, he2⟩ := hM k (h.comp (g.comp f))
    haveI : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap (h.comp (g.comp f)) ≫ hU.fromSpec) A) :=
      Module.Finite.equiv e2.symm
    rw [GlobalTheory.T.lieMult_iff_finrank_simultaneousEigenSubmodule _ _ _ _ _ _ _ _ inferInstance, finrank_eigSub_transport _ _ e2 he2]

theorem lieHerMat_iff_le {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {B : Type}
    [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K₂ : Ideal B)
    (hK₂ : ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f))
    {T : Type} [CommRing T] (f : B →+* T) :
    LieHerMat b M f (f.comp βB) ↔ lieIdeal b βB M ⊔ K₂ ≤ RingHom.ker f := by
  constructor
  · intro h
    obtain ⟨hL, hR⟩ := h T (RingHom.id T)
    have hJ : lieIdeal b βB M ≤ RingHom.ker f := (GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker _ _ _ b _ βB n M T f).1 hL
    exact sup_le hJ ((hK₂ T f hJ).1 hR)
  · intro hK T' _ g
    have hker : RingHom.ker f ≤ RingHom.ker (g.comp f) := fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, hx, map_zero]
    have hJ : lieIdeal b βB M ≤ RingHom.ker (g.comp f) := le_sup_left.trans (hK.trans hker)
    have h2 : K₂ ≤ RingHom.ker (g.comp f) := le_sup_right.trans (hK.trans hker)
    exact ⟨(GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker _ _ _ b _ βB n M T' (g.comp f)).2 hJ, (hK₂ T' (g.comp f) hJ).2 h2⟩

theorem lieHer_ideal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : OActN D.O A) (z : S),
  ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'), spMap f ≫ hU.fromSpec ≫ s = spMap β →
      (LieHer b act β (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) := by
  intro p _ D R _ b S s A _ _ hA act z
  obtain ⟨U, hU, hz, n, M, hM⟩ := GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group (𝓞 D.F) S A hA (act.toF D) z
  obtain ⟨βB, hβB⟩ := exists_baseMap s hU
  obtain ⟨K₂, hK₂⟩ := GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition p D R b Γ(S, U) βB n M
  refine ⟨U, hU, hz, lieIdeal b βB M ⊔ K₂, fun R' _ f β hc => ?_⟩
  obtain rfl := hβB R' f β hc
  rw [lieHer_iff_mat b act hU M hM f]
  exact lieHerMat_iff_le b βB M K₂ hK₂ f

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelExtends
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm GlobalTheory.HtGen GlobalTheory.RootFrameB
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

namespace GlobalTheory.LabelExt

section Gen

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem lift_finite [IsIntegrallyClosed R] {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] (y : Sp R ⟶ S) (w : Sp K ⟶ X)
    (h : w ≫ f = spMap (algebraMap R K) ≫ y) : ∃ v : Sp R ⟶ X, v ≫ f = y ∧ spMap (algebraMap R K) ≫ v = w :=
  _root_.UpperTheory.Reformulated.B.Yt7.lift_finite f y w h

theorem ext_frac {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {y : Sp R ⟶ S} {u v : Over.mk y ⟶ G}
    (h : spMap (algebraMap R K) ≫ u.left = spMap (algebraMap R K) ≫ v.left) : u = v := by
  haveI : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  ext1
  exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w u, Over.w v]) (spMap (algebraMap R K)) h

theorem lift_tors [IsIntegrallyClosed R] {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) {q : ℕ}
    (hq : q ≠ 0) {y : Sp R ⟶ S} {y' : Sp K ⟶ S} (hy : spMap (algebraMap R K) ≫ y = y') (w : Over.mk y' ⟶ G)
    (hw : w ^ q = 1) : ∃ v : Over.mk y ⟶ G, spMap (algebraMap R K) ≫ v.left = w.left := by
  haveI := (AbTorsionAnyBase.isFinite_and_flat_torsion S G hG q (Nat.one_le_iff_ne_zero.2 hq)).1
  have e : w ≫ mulN G q = CartesianMonoidalCategory.toUnit _ ≫ η[G] := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hw]; rfl
  let w₁ : Over.mk y' ⟶ torsion G q := Limits.pullback.lift w _ e
  have h₁ : w₁ ≫ torsion.ι G q = w := Limits.pullback.lift_fst _ _ _
  obtain ⟨v, hv, hv'⟩ := lift_finite (torsion G q).hom y w₁.left ((Over.w w₁).trans hy.symm)
  refine ⟨(Over.homMk v hv : Over.mk y ⟶ torsion G q) ≫ torsion.ι G q, ?_⟩
  rw [← h₁, Over.comp_left, Over.comp_left, ← hv', Category.assoc]
  rfl

end Gen

end GlobalTheory.LabelExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledUnitaryTraitsLatticesEquivConnectedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.Poinc.FibLat

namespace GlobalTheory.UPoinc.GFib

theorem TT_le_HH_of_uIsLab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} (X : USetup C) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy)
    (hker : yy.ker = X.S.HH X.M z) : X.S.TT X.M z ≤ X.S.HH X.M z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hlab, -⟩ := h
  have hk : lb.yy.ker ≤ yy.ker := fun a ha => by
    have h0 : lb.yy a = QuotientAddGroup.mk 0 := by rw [AddMonoidHom.mem_ker.1 ha]; rfl
    have := hlab a 0 h0
    rw [map_zero] at this
    exact AddMonoidHom.mem_ker.2 this
  intro t ht
  rw [← hker]
  refine hk ?_
  have h1 : t ∈ (X.S.rechart c₀ hc R' fg frac hth hev).perp lb.yy.ker := fun h hh => ht h (hker ▸ hk hh)
  have h2 := lb.isoFree.1 h1
  rwa [ThetaSys.perp_perp] at h2

end GlobalTheory.UPoinc.GFib

theorem GlobalTheory.UPoinc.GFib.labelled_lattices_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p _ z hz ct ct' y y' hy hy' yy yy' hl hl'
  have hker := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct yy hl.uIsLab
  have hker' := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct' yy' hl'.uIsLab
  have hTH := GlobalTheory.UPoinc.GFib.TT_le_HH_of_uIsLab X ct yy hl.uIsLab hker.2
  obtain ⟨f, gγ, hf, hg⟩ := GlobalTheory.T.unitaryEndomorphisms_torsion_extend_semiAbelian E H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO hE hpt z hTH
  have hL : 0 < X.S.r * X.S.N := Nat.mul_pos (by have := X.S.r_pos; omega) (by have := X.S.N_ge; omega)
  have hprim : IsPrimitiveRoot (X.S.ζ ^ (X.S.r * X.S.N)) (X.S.r * X.S.N) :=
    X.S.prim.pow (by positivity) (by ring)
  let ζ : X.o₁ˣ := (hprim.isUnit hL.ne').unit
  have hζ : IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) := hprim
  obtain ⟨s, σ, hs, hσ, hc⟩ :=
    GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre E H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p z f gγ hf hg ζ hζ
  obtain ⟨c, hc1, hc2⟩ := hc ct y hy yy hl
  obtain ⟨c', hc1', hc2'⟩ := hc ct' y' hy' yy' hl'
  have hx : q.base (y (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy, ct.cen]
  have hx' : q.base (y' (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy', ct'.cen]

  have hrk : ∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt FinalForm.G w r₀ := by
    obtain ⟨r₀, -, ⟨e₀⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE (y (cPt p))
    refine ⟨r₀, fun w hw => ?_⟩
    obtain ⟨r, hr, ⟨e⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE w
    have hT : X.S.TT Y w = X.S.TT Y (y (cPt p)) := by
      simp only [ThetaSys.TT]
      rw [GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv w,
        GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv (y (cPt p))]
      simp only [hw, hx]
    have e₁ : (Fin r → ZMod (X.S.r * X.S.N)) ≃ (Fin r₀ → ZMod (X.S.r * X.S.N)) :=
      (e.symm.toEquiv.trans (Equiv.setCongr (congrArg (fun H : AddSubgroup X.S.Gam => (H : Set X.S.Gam)) hT))).trans
        e₀.toEquiv
    haveI : NeZero (X.S.r * X.S.N) := ⟨hL.ne'⟩
    have hcard := Fintype.card_congr e₁
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have h2 : 2 ≤ X.S.r * X.S.N := by
      have := X.S.r_pos; have := X.S.N_ge; nlinarith
    rwa [Nat.pow_right_injective h2 hcard] at hr
  have hmove := GlobalTheory.T.characterLatticeAtFibre_const_preconnected X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi _ q z hz hrk (𝓞 E) _ f (fun a => (hf a).1) gγ ζ
    (X.S.r * X.S.N) hL (Units.ext (by simpa using hζ.pow_eq_one)) X.S.unit (fun t => (hg t).1)
    (fun t w hw => (hg t).2.2 w hw) ct.T.P.D.toPre.X _ c _ _ hx hx' hc1
  haveI : IsDomain X.o₁ := (inferInstance : GlobalTheory.ZH.ArithBase X.o₁ X.Ω₁).ded.toIsDomain
  obtain ⟨θ, hθm, hθc⟩ := GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi (𝓞 E) _ f gγ ζ (X.S.r * X.S.N) hL hζ
    X.S.unit ct.T.P.D.toPre.X ct'.T.P.D.toPre.X _ c _ c' _ hmove hc1'
  refine ⟨θ, fun a v hv => ?_, fun a v => ?_⟩
  · obtain ⟨a', ha'⟩ := hker'.1 (QuotientAddGroup.mk (θ v))
    have hd : a' - a ∈ X.S.HH X.M z := by
      rw [← ThetaSys.perp_TT]
      refine ThetaSys.mem_perp'.2 fun t ht => ?_
      have e1 := hc2' a' (θ v) ⟨t, ht⟩ ha'
      rw [hθc, hc2 a v ⟨t, ht⟩ hv] at e1
      have e2 := hs.mul_left_cancel e1
      rw [sub_eq_add_neg, eStd_add_right, eStd_neg_right, ← e2]
      exact add_neg_cancel _
    rw [← hker'.2, AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hd
    rw [← hd, ha']
  · obtain ⟨b, rfl⟩ := hσ a
    exact hθm b v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPart
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CentLev

theorem loc_cpt_part {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : UL n w) (hs : y.1.val.charpoly.Separable) :
    ∃ C : Set (UL n w), IsCompact C ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ C := by
  obtain ⟨Ω, hΩ, hmem⟩ := GlobalTheory.CentCpt.main E hU n w y hs
  haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a * y = y * a := ha
    have hb' : b * y = y * b := hb
    have hav : (a : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (a : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) ha'; simpa using this
    have hbv : (b : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (b : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) hb'; simpa using this
    have := GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hs hav hbv
    apply Subtype.ext; apply Units.ext; simpa using this
  refine ⟨Ω, hΩ, fun z hz => ?_⟩
  obtain ⟨hzT, hzc⟩ := GlobalTheory.LocFinU.cptPart_subset_of_comm _ hc hz
  exact hmem z hzT hzc

theorem stab_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU E n, twCent (MonoidHom.id (finU E n)) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU E n)) (finPt γ)) ∧ (twCent (MonoidHom.id (finU E n)) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU E n)) (finPt γ))) ≠ 0 := by
  intro E _ _ _ hU n hn S hS K' hK' γ hγ x
  set δ : finU E n := finPt γ with hδ
  set T := twCent (MonoidHom.id (finU E n)) δ with hT
  let ρ : ∀ w : Pl E, finU E n →* UL n w := fun w =>
    { toFun := fun z => ⟨cLoc w (z : UA E n), GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hρv : ∀ w z, ((ρ w z : UL n w) : GLw n w) = cLoc w (z : UA E n) := fun _ _ => rfl
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    continuous_induced_rng.2 ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)
  have hδw : ∀ w, ((ρ w δ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
    intro w
    rw [hρv, hδ, FinPtLoc.finPt_eq]
    apply Units.ext
    refine Matrix.ext fun i j => ?_
    change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
    rw [FinPtLoc.snd_entry]
    rfl
  have hsep : ∀ w, ((ρ w δ : UL n w) : GLw n w).val.charpoly.Separable := by
    intro w
    rw [hδw]
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = γ.1.val.map (algebraMap E _) := rfl
    rw [e, Matrix.charpoly_map]
    exact hγ.map
  have hsetK : ∀ K'' : ∀ w : Pl E, Subgroup (UL n w), (globLev S K'' : Set (finU E n)) =
      {z : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ (K'' w : Set (UL n w))} := by
    intro K''
    ext z
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    refine forall₂_congr fun w _ => ?_
    rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
    constructor
    · rintro ⟨a, ha, e⟩
      have : a = ⟨_, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (z : UA E n)⟩ := Subtype.ext e
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hKc : IsCompact (globLev S (KL n) : Set (finU E n)) := by
    rw [hsetK]
    exact GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => (KL n w : Set (UL n w)))
      (fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2) (Filter.Eventually.of_forall fun _ => rfl)
  have hcf : ⇑((MulAut.conj x).toMonoidHom) = fun g : finU E n => x * g * x⁻¹ := by
    ext g; simp
  have hconj : ∀ H : Subgroup (finU E n), (H.map (MulAut.conj x).toMonoidHom : Set (finU E n)) =
      (fun g => x⁻¹ * g * x) ⁻¹' (H : Set (finU E n)) := by
    intro H; ext g
    rw [Subgroup.coe_map, hcf]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  refine ⟨?_, ?_⟩
  · rintro t ⟨htT, htK⟩
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hKx : IsCompact ((globLev S (KL n)).map (MulAut.conj x).toMonoidHom : Set (finU E n)) := by
      rw [Subgroup.coe_map, hcf]
      exact hKc.image (by fun_prop)
    exact hKx.closure_of_subset fun s hs => Subgroup.zpowers_le.2 htK hs
  · have hUo : IsOpen ((globLev S K').map (MulAut.conj x).toMonoidHom : Set (finU E n)) := by
      rw [hconj]
      exact (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK').preimage (by fun_prop)
    choose C0 hC0c hC0 using fun w => loc_cpt_part hU n w (ρ w δ) (hsep w)
    have hcof := GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ
    let C : ∀ w : Pl E, Set (UL n w) := fun w =>
      if cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w then (KL n w : Set (UL n w)) else C0 w
    have hCc : ∀ w, IsCompact (C w) := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
      · simp only [C, if_neg h]; exact hC0c w
    have hCK : ∀ᶠ w in cofinite, C w = KL n w := by
      filter_upwards [hcof] with w hw
      have e : ρ w δ = locPt w γ := by
        rw [← GlobalTheory.BCT.locPt_finPt E hU n γ w, FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
        rfl
      have hw' : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w := by rw [e]; exact hw
      simp only [C, if_pos hw']
    have hsub : ∀ w, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) : Set (UL n w)) ⊆ C w := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact h
      · simp only [C, if_neg h]; exact hC0 w
    have hD := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS C hCc hCK
    have hle : cptPart T ≤ ⨅ w : Pl E, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ))).comap (ρ w) := by
      rw [cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      rw [SetLike.mem_coe, Subgroup.mem_iInf]
      intro w
      rw [Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · have ht' : t * δ = δ * t := htT
        show ρ w t * ρ w δ = ρ w δ * (MonoidHom.id _) (ρ w t)
        rw [MonoidHom.id_apply, ← map_mul, ht', map_mul]
      · have himc : IsCompact (ρ w '' closure (Subgroup.zpowers t : Set (finU E n))) := htc.image (hρc w)
        refine himc.closure_of_subset ?_
        rintro _ ⟨k, rfl⟩
        exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have hTD : (cptPart T : Set (finU E n)) ⊆
        {z : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ C w} := by
      intro z hz w _
      have hzw := Subgroup.mem_iInf.1 (hle hz) w
      rw [Subgroup.mem_comap] at hzw
      rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
      exact hsub w hzw
    have hUo' : IsOpen ((((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) : Subgroup _) :
        Set (cptPart T)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hUo.preimage continuous_subtype_val
    have hfi := GlobalTheory.LocVec.finiteIndex_of_isOpen (cptPart T) hD hTD _ hUo'
    have hTc : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
    have heq : (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) =
        ((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hTc z.2, h⟩⟩
    rw [Subgroup.relIndex, heq]
    exact hfi.index_ne_zero

end GlobalTheory.BCT.CentLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearRelationMixedDensitiesIntegralsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_relation_mixed_densities_integrals : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (L : J → Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ i, a i * dens (L i) c y = 0) → ∀ f : CxPts p σ → ℝ, (∀ i, Intg (L i) f) → ∑ i, a i * Mix.int (L i) f = 0 := by
  first | exact @GlobalTheory.Mix.sum_int_eq_zero_of_dens | exact GlobalTheory.Mix.sum_int_eq_zero_of_dens | (intros; apply GlobalTheory.Mix.sum_int_eq_zero_of_dens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLatticePointsQuadraticBallEstimateStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_lattice_points_quadratic_ball_estimate : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → 2 * Fintype.card ι * ρ ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  first | exact @GlobalTheory.HSAmp.log_ellCount_near | exact GlobalTheory.HSAmp.log_ellCount_near | (intros; apply GlobalTheory.HSAmp.log_ellCount_near <;> assumption)
end

