import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0329

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZPartEig

theorem heckePolyOf_coeff {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) {k : ℕ} (hk : k ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff k = (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k := by
  classical
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

theorem heckePolyOf_val_eq {L : Type} [Field L] [CharZero L] (n q : ℕ) (hq : q ≠ 0) (a b : ℕ → L)
    (h : Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b) {k : ℕ} (hk : k ≤ n) : a k = b k := by
  have e := congrArg (fun p => Polynomial.coeff p k) h
  simp only [heckePolyOf_coeff n q _ hk] at e
  have hne : ((-1 : L) ^ k * (q : L) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ hne e

theorem apply_of_mem_maxGen {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : K →+* ℂ) (j : V →ₛₗ[σ] H) (T : Module.End K V)
    (N : Module.End ℂ H) (hN : Commute N (LinearMap.adjoint N)) (hj : ∀ f, j (T f) = N (j f)) (c : K) (f : V)
    (hf : f ∈ T.maxGenEigenspace c) : N (j f) = σ c • j f := by
  have key : ∀ (k : ℕ) (g : V), j (((T - c • (1 : Module.End K V)) ^ k : Module.End K V) g) =
      (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j g)) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hj, map_smulₛₗ]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have h0 : (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j f)) = 0 := by rw [← key, hk, map_zero]
  have hmem : j f ∈ N.maxGenEigenspace (σ c) := (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, h0⟩
  rw [GlobalTheory.NormalFamily.maxGenEigenspace_eq hN] at hmem
  exact Module.End.mem_eigenspace_iff.1 hmem

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OpLab (R : RealDat3 D A3 Ks) (i : Fin D.R.m) : (A3.liftI i A3.A.μ0).OpIx → Pl D.host.E → List ℤ → Prop :=
  Sum.elim
    (fun k P d => R.pl ((A3.A.fam.L i A3.A.μ0).pl k.1) = P ∧ k.2 ≤ (Vc D i).rank ∧ d = splitLab (Vc D i).rank k.2)
    (fun k P d => R.plI ((A3.liftI i A3.A.μ0).plI k.1) = P ∧ Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 ∧
      d = GlobalTheory.Hk3.labIn (Vc D i).rank k.2)

theorem opLab_ops (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h) :
    ∀ idx P d, OpLab R i idx P d → GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧
      ∀ f, R.jV i A3.A.μ0 ((A3.liftI i A3.A.μ0).opAll idx f) = h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) := by
  have hlev := hC.base.lev
  have hfam := hC.base.fam
  have hmod := hC.base.models
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.1
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨⟨Q, hQ⟩, s'⟩) P d hc
  · obtain ⟨rfl, hk, rfl⟩ := hc
    refine ⟨((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hlev).2.2.2 hfam A3.A.μ0 P' hP').1, fun f => ?_⟩
    exact (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hlev hfam hmod).2 i A3.A.μ0 h hh ⟨P', hP'⟩ k hk f
  · obtain ⟨rfl, hs, rfl⟩ := hc
    have hty : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 →
        GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 (R.plI k.1) ∧ Formalism.DivisionValues.conjPl (R.plI k.1) = R.plI k.1 ∧
          (GlobalTheory.Hk3.labIn (Vc D i).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
      ⟨(c3 A3.A.μ0 k.1 k.1.2).1, (c3 A3.A.μ0 k.1 k.1.2).2,
        ((GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
    refine ⟨(c3 A3.A.μ0 Q hQ).1, fun f => ?_⟩
    exact (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hlev hfam hmod i A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D i).rank k.2) (A3.heckeLI i A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) hty (hC.inert.hL i A3.A.μ0).some (⟨Q, hQ⟩, s') hs).2.2.2 h hh f

theorem exists_opLab (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d → ∃ idx, OpLab R i idx P d := by
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.2.1
  intro P d hg hr
  rcases hr with ⟨hc, k, hk, rfl⟩ | ⟨hc, hl⟩
  · obtain ⟨P0, hP0, rfl⟩ := (c3 P hg).2 hc
    exact ⟨Sum.inl (⟨P0, hP0⟩, k), rfl, hk, rfl⟩
  · obtain ⟨Q, hQ, rfl⟩ := (c3 P hg).1 hc
    obtain ⟨hlen, hpw, hdual⟩ := (GlobalTheory.LabChar.labels_char (Vc D i) _ d).1 hl
    obtain ⟨s', h1, h2, h3, rfl⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank d).1 ⟨hlen, hpw, hdual hc⟩
    exact ⟨Sum.inr (⟨Q, hQ⟩, s'), rfl, ⟨h2, h3, h1⟩, rfl⟩

theorem opLab_val_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) :
    ∀ idx P d, OpLab R i idx P d → ∀ y y', (A3.liftI i A3.A.μ0).HasRes3 q y → (A3.liftI i A3.A.μ0).HasRes3 q y' →
      y idx = y' idx := by
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨Q, s'⟩) P d hc y y' hy hy'
  · obtain ⟨-, hk, -⟩ := hc
    have hq : (A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩ ≠ 0 := by
      show A3.A.q P' ≠ 0
      rw [((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.base.lev).2.2.2 hC.base.fam A3.A.μ0 P' hP').2.2]
      exact fun h0 => (R.pl P').ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y (Sum.inl (⟨P', hP'⟩, j))) =
        Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y' (Sum.inl (⟨P', hP'⟩, j))) :=
      (hy.1 ⟨P', hP'⟩).trans (hy'.1 ⟨P', hP'⟩).symm
    have hk' : k ≤ (A3.A.fam.L i A3.A.μ0).n := by
      have e2 : (A3.A.fam.L i A3.A.μ0).n = A3.A.r + A3.A.t := rfl
      rw [e2, ← R.B.rankL i]; exact hk
    exact heckePolyOf_val_eq _ _ hq _ _ e hk'
  · exact (hy.2 (Q, s')).trans (hy'.2 (Q, s')).symm

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thetaLiftPoint_mem_jointEigenspace_of_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : (R.toCx3 F).H3W F.cr false) (i : Fin D.R.m)
    (p : A3.fam3.base3.Ix) (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL)
    (hx : (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p) :
    F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1) := by
  have hZ := (hW i p x).2 hx
  have h2 : (A3.A.fam.L i A3.A.μ0).vE (A3.A.fam.lvlA F.P0 F.ψ0) *ᵥ
      ((A3.A.fam.L i A3.A.μ0).zE (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0) *ᵥ x) ∈
      ((A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1)).map
        ((A3.A.fam.L i A3.A.μ0).S.basis.equivFun : (A3.A.fam.L i A3.A.μ0).S.Forms →ₗ[D.what₂.LL] _) := hZ
  obtain ⟨g, hg, hge⟩ := Submodule.mem_map.1 h2
  convert hg using 1
  rw [← LinearEquiv.symm_apply_apply (A3.A.fam.L i A3.A.μ0).S.basis.equivFun g]
  erw [hge]
  rfl

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def eigVal (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) (P : Pl D.host.E) (d : List ℤ) :
    D.what₂.LL :=
  if hx : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d then hx.1.choose hx.2.choose else 0

theorem eig_of_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ))
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h)
    (hn : GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0) h) (f : (A3.A.fam.L i A3.A.μ0).S.Forms)
    (hf : f ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d →
      h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) = D.what₂.embLL (eigVal R i q P d) • R.jV i A3.A.μ0 f := by
  let E : Submodule ℂ (R.HV i A3.A.μ0).H :=
    ⨅ (P : Pl D.host.E) (d : List ℤ) (_ : GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ RelLab (Vc D i) P d),
      (h P (Finsupp.single d 1)).eigenspace (D.what₂.embLL (eigVal R i q P d))
  have hle : (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q ≤ E.comap (R.jV i A3.A.μ0) := by
    unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
    refine iSup₂_le fun y hy g hg => ?_
    rw [Submodule.mem_comap]
    simp only [E, Submodule.mem_iInf]
    rintro P d ⟨hgd, hr⟩
    have hex : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d :=
      ⟨⟨y, hy⟩, exists_opLab R F hC i P d hgd hr⟩
    have ha : eigVal R i q P d = hex.1.choose hex.2.choose := by
      unfold eigVal
      rw [dif_pos hex]
    have ha' : eigVal R i q P d = y hex.2.choose :=
      ha.trans (opLab_val_eq R F hC i q _ P d hex.2.choose_spec _ _ hex.1.choose_spec hy)
    have hop := opLab_ops R F hC i h hh _ P d hex.2.choose_spec
    have hN : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) :=
      (congrArg (Commute (h P (Finsupp.single d 1))) (hn.2 P hop.1 (Finsupp.single d 1))).mpr (hn.1 P P hop.1 hop.1 _ _)
    have key := apply_of_mem_maxGen D.what₂.embLL (R.jV i A3.A.μ0) ((A3.liftI i A3.A.μ0).opAll hex.2.choose) _ hN hop.2
      (y hex.2.choose) g (Formalism.L2.Col.eigAt_le (A3.liftI i A3.A.μ0).opAll y hex.2.choose hg)
    exact Module.End.mem_eigenspace_iff.2 (key.trans (congrArg (fun c => D.what₂.embLL c • R.jV i A3.A.μ0 g) ha'.symm))
  intro P d hg hr
  have e1 := hle hf
  rw [Submodule.mem_comap] at e1
  simp only [E, Submodule.mem_iInf] at e1
  exact Module.End.mem_eigenspace_iff.1 (e1 P d ⟨hg, hr⟩)

theorem points_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s _hOk hC hW i p
  obtain ⟨h, hh, hn⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models).2 i A3.A.μ0
  refine ⟨eigVal R i (A3.fam3.tr3 i p.1), fun x hx => ?_⟩
  have hm := thetaLiftPoint_mem_jointEigenspace_of_part R F hW i p x hx
  intro P d hg hr
  have e1 := eig_of_mem R F hC i _ h hh hn _ hm P d hg hr
  have e2 := hh P hg (Finsupp.single d 1) (R.jV i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x))
  exact e2.symm.trans ((congrArg (R.HV i A3.A.μ0).e e1).trans (map_smul _ _ _))

end GlobalTheory.ZPartEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessOrthogonalLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_orthogonal_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, thPair μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1 := by
  first | exact @GlobalTheory.MatCoefLevel.matCoef_level | exact GlobalTheory.MatCoefLevel.matCoef_level | (intros; apply GlobalTheory.MatCoefLevel.matCoef_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffPolynomialDecayRealDirectionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMatrixCoeff_polynomialDecay_realDirections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  first | exact @GlobalTheory.RealDecay.realDecay | exact GlobalTheory.RealDecay.realDecay | (intros; apply GlobalTheory.RealDecay.realDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerRestrict

variable {D : D7}

section Maps
variable {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)

theorem isoPart_add (y y' : Mx D W.rank r) : isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' :=
  Matrix.add_mul _ _ _

theorem isoPart_zero : isoPart V W C (0 : Mx D W.rank r) = 0 := Matrix.zero_mul _

theorem midPart_add (x x' : WO V' W) : midPart V V' W B (x + x') = midPart V V' W B x + midPart V V' W B x' :=
  Matrix.add_mul _ _ _

theorem midPart_zero : midPart V V' W B (0 : WO V' W) = 0 := Matrix.zero_mul _

theorem continuous_isoPart : Continuous (isoPart V W C : Mx D W.rank r → WO V W) :=
  continuous_id.matrix_mul continuous_const

theorem continuous_midPart : Continuous (midPart V V' W B : WO V' W → WO V W) :=
  continuous_id.matrix_mul continuous_const

theorem isoPart_rat {γ : Mx D W.rank r} (h : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨γ₀, rfl⟩ := h
  exact ⟨γ₀ * (adj D C * V.gram), by
    show (γ₀ * (adj D C * V.gram)).map (incA D) = _
    rw [Matrix.map_mul]; rfl⟩

theorem midPart_ratW (γ : Matrix (Fin W.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B (ratW W V' γ) = ratW W V (γ * (V'.gram⁻¹ * adj D B * V.gram)) := by
  unfold midPart ratW
  simp only [Matrix.map_mul]

theorem midPart_infPart {u : WO V' W} (hu : u.map (infPart D) = 0) : (midPart V V' W B u).map (infPart D) = 0 := by
  unfold midPart
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

def midHom : WO V' W →+ WO V W where
  toFun := midPart V V' W B
  map_zero' := midPart_zero B
  map_add' := midPart_add B

end Maps

section Shift
variable {m n : ℕ}

theorem lattice_Mx (D : D7) (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem setIntegral_add_right {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓨)
    (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) (b : Mx D m n) :
    ∫ a in 𝓨, φ (a + b) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  have : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, h𝓨, -⟩ := h
  have e1 : ∫ a in 𝓨, φ (a + b) ∂μ = ∫ a in b +ᵥ 𝓨, φ a ∂μ := by
    rw [← Set.image_vadd]
    simp only [vadd_eq_add]
    rw [(measurePreserving_add_left μ b).setIntegral_image_emb (MeasurableEquiv.addLeft b).measurableEmbedding]
    simp only [add_comm b]
  rw [e1]
  exact (h𝓨.vadd_of_comm b).setIntegral_eq h𝓨 fun γ a => hφ γ γ.2 a

end Shift

section Main
variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {ψ : AddChar (AF D.host.F) ℂ}

theorem sympl_mid (hs : IsIsoSplit V V' C B) (y : Mx D W.rank r) (x x₀ : WO V' W) :
    symplOH V W (isoPart V W C y + midPart V V' W B x) (midPart V V' W B x₀) = symplOH V' W x x₀ := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs y 0 x x₀
  rwa [isoPart_zero, zero_add] at this

theorem sympl_iso (hs : IsIsoSplit V V' C B) (y y₀ : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y₀) = 0 := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs y y₀ x 0
  rwa [midPart_zero, add_zero, GlobalTheory.ThetaSquare.symplOH_zero_right] at this

theorem sympl_mid_left (hs : IsIsoSplit V V' C B) (y : Mx D W.rank r) (x x₀ : WO V' W) :
    symplOH V W (midPart V V' W B x₀) (isoPart V W C y + midPart V V' W B x) = symplOH V' W x₀ x := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs 0 y x₀ x
  rwa [isoPart_zero, zero_add] at this

theorem sympl_iso_left (hs : IsIsoSplit V V' C B) (y y₀ : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C y₀) (isoPart V W C y + midPart V V' W B x) = 0 := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs y₀ y 0 x
  rwa [midPart_zero, add_zero, GlobalTheory.ThetaSquare.symplOH_zero_left] at this

theorem periodic_iso (hs : IsIsoSplit V V' C B) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W)
    (γ : Mx D W.rank r) (hγ : γ ∈ ratMx D W.rank r) (y : Mx D W.rank r) :
    f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  obtain ⟨γ₀, hγ₀⟩ := isoPart_rat (V := V) C hγ
  have e := hf.quasi γ₀ (isoPart V W C y + midPart V V' W B x)
  change ratW W V γ₀ = isoPart V W C γ at hγ₀
  rw [hγ₀, sympl_iso_left hs, neg_zero, ψ.map_zero_eq_one, one_mul, ← add_assoc, ← isoPart_add] at e
  exact e

theorem res_heis_mid (hs : IsIsoSplit V V' C B) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (f : WO V W → ℂ) (x₀ : WO V' W) :
    res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x₀) f) = heisO ψ V' W x₀ (res V V' W C B μ 𝓨 f) := by
  funext x
  simp only [res, heisO]
  simp only [sympl_mid hs, add_assoc, ← midPart_add]
  exact integral_const_mul _ _

theorem res_heis_iso (hs : IsIsoSplit V V' C B) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (y₀ : Mx D W.rank r) :
    res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C y₀) f) = res V V' W C B μ 𝓨 f := by
  funext x
  simp only [res, heisO]
  simp only [sympl_iso hs, ψ.map_zero_eq_one, one_mul]
  have e : ∀ y, isoPart V W C y + midPart V V' W B x + isoPart V W C y₀ =
      isoPart V W C (y + y₀) + midPart V V' W B x := fun y => by rw [isoPart_add]; abel
  simp only [e]
  exact setIntegral_add_right h (fun y => f (isoPart V W C y + midPart V V' W B x))
    (fun γ hγ y => periodic_iso hs hf x γ hγ y) y₀

theorem integrable_res (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    IntegrableOn (fun y => f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ := by
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  obtain ⟨c, hc⟩ := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1 f hf |>.2.1
  refine Measure.integrableOn_of_bounded (M := c) (by rw [h.2.2]; exact ENNReal.one_ne_top) ?_
    (Filter.Eventually.of_forall fun y => hc _)
  exact (hf.cont.comp ((continuous_isoPart C).add continuous_const)).aestronglyMeasurable

theorem continuous_res (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    Continuous (res V V' W C B μ 𝓨 f) := by
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓨) := isFiniteMeasure_restrict.2 (by rw [h.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨c, hc⟩ := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1 f hf |>.2.1
  obtain ⟨-, -, i3, -⟩ := lattice_Mx D W.rank V'.rank
  have : FirstCountableTopology (WO V' W) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  exact continuous_of_dominated (bound := fun _ => c)
    (fun x => (hf.cont.comp ((continuous_isoPart C).add continuous_const)).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun y => hc _) (integrable_const c)
    (Filter.Eventually.of_forall fun y => hf.cont.comp (continuous_const.add (continuous_midPart B)))

theorem res_quasi (hs : IsIsoSplit V V' C B) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (γ : Matrix (Fin W.rank) (Fin V'.rank) D.host.E) (x : WO V' W) :
    res V V' W C B μ 𝓨 f (ratW W V' γ + x) = ψ (-(symplOH V' W (ratW W V' γ) x)) * res V V' W C B μ 𝓨 f x := by
  simp only [res]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e := hf.quasi (γ * (V'.gram⁻¹ * adj D B * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [← midPart_ratW, sympl_mid_left hs] at e
  simp only
  rw [← e, midPart_add]
  congr 1
  abel

theorem res_level (hs : IsIsoSplit V V' C B) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) : ∃ U : AddSubgroup (WO V' W), IsOpen (U : Set (WO V' W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V' W u (res V V' W C B μ 𝓨 f) = res V V' W C B μ 𝓨 f := by
  obtain ⟨U, hU, hfix⟩ := hf.level
  refine ⟨U.comap (midHom B), hU.preimage (continuous_midPart B), fun u hu h0 => ?_⟩
  have e := hfix (midPart V V' W B u) hu (midPart_infPart B h0)
  rw [← res_heis_mid hs, e]

end Main

theorem res_theta : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → (∀ f, IsThetaFunO ψ V W f → (∀ x, IntegrableOn (fun y => f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧ IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f) ∧ (∀ x, res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) = heisO ψ V' W x (res V V' W C B μ 𝓨 f)) ∧ ∀ y, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C y) f) = res V V' W C B μ 𝓨 f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 h
  have hF := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs
  refine ⟨fun f hf => ⟨integrable_res hψ h hf, ⟨fun γ x => res_quasi hs μ 𝓨 hf γ x, res_level hs μ 𝓨 hf,
    continuous_res hψ h hf, GlobalTheory.T.thetaRestriction_isotropicSplit_smooth_realPoints D V V' W r C B hF ψ hψ μ 𝓨 h f hf⟩,
    fun x => res_heis_mid hs μ 𝓨 f x, fun y => res_heis_iso hs h hf y⟩, GlobalTheory.T.exists_thetaFunction_isotropicRestriction_ne_zero D V V' W r C B hs hF ψ hψ μ 𝓨 h⟩

end GlobalTheory.TowerRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedMatrixCoefficientInAdaptedFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  first | exact @GlobalTheory.PackLoc.mco_frame | exact GlobalTheory.PackLoc.mco_frame | (intros; apply GlobalTheory.PackLoc.mco_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlaceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (radical)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_function_constant_term_vanish_split_place : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (a : ℕ), 0 < a → a < V.rank → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin V.rank) (ResF v)) W), τ.IsIrreducible → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ (radical (ResF v) V.rank a) → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) [μ.IsHaarMeasure], ∀ φ ∈ CcLoc D.sp.cm.sig V.gram v, ∀ f : GLoc D.sp.cm.sig V.gram v → ℂ, (f = conv μ (s.idem μ τ) φ ∨ f = conv μ φ (s.idem μ τ)) → ∀ g : GL (Fin V.rank) (Fv D.host.F v), ∃ H : Subgroup (GLoc D.sp.cm.sig V.gram v), IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v)) ∧ (∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a) ∧ ∃ ν : Measure H, ν.IsHaarMeasure ∧ ∀ x y, ∫ u : H, f (x * u * y) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | exact GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | (intros; apply GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumConjugationDictionaryRowGridStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_conjugation_dictionary_row_grid : GlobalTheory.SepRows.DepFixed → All fun {D} _ {L} _ {G} W _ => ∀ i, i < D.R.m → IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧ IsWeilDatumO W.ψ _ _ (G.chrS (.core i))⁻¹ (G.chrT (.core i))⁻¹ (omCore W i) ∧ (∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)) ∧ (∀ f, VacG W.ψ _ _ (latCore G i) f ↔ Dep W (.core i) (star f)) ∧ (∀ g h f, omRow W i (g, h) f = star (W.om (.chi i 0) (negGA _ g, h) (star f))) ∧ (∀ g h f, omCore W i (g, h) f = star (W.om (.core i) (negGA _ g, h) (star f))) ∧ ∀ f, VacG W.ψ _ _ (latRow G i) f → ∀ k ∈ lev G (.grid i 0), omRow W i (1, k) f = f := by
  first | exact @GlobalTheory.ConjDict.conj_dict | exact GlobalTheory.ConjDict.conj_dict | (intros; apply GlobalTheory.ConjDict.conj_dict <;> assumption)
end

