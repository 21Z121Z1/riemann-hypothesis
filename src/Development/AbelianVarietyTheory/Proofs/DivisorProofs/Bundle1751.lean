import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph.Scal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem disc_sub_sq_notMem (v : Pl F) (b c t : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal) : t ^ 2 - (b ^ 2 - 4 * c) ∉ v.asIdeal := by
  intro h
  obtain ⟨s, a, ha, hs⟩ := v.isMaximal.exists_inv h2
  apply hroot (s * (t - b))
  have h4 : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) ∈ v.asIdeal := by
    have e : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) =
        (t ^ 2 - (b ^ 2 - 4 * c)) + a * ((t - b) * (a * (t - b) - 2 * t)) := by
      have : a = 1 - s * 2 := by linear_combination hs
      subst this
      ring
    rw [e]
    exact add_mem h (Ideal.mul_mem_right _ _ ha)
  exact ((v.isPrime.mem_or_mem ((v.isPrime.mem_or_mem h4).resolve_left h2)).resolve_left h2)

theorem exists_delta (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : Pl F) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ (δ : 𝓞 E) (D : 𝓞 F), σ (δ : E) = -(δ : E) ∧ (δ : E) * δ = algebraMap F E (D : F) ∧ D ∉ v.asIdeal ∧
      1 - D ∉ v.asIdeal := by
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hin]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hc, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hσ v hp
  have hδ : ((2 * a + algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = 2 * (a : E) + algebraMap F E (b : F) := rfl
  have hD : ((b ^ 2 - 4 * c : 𝓞 F) : F) = (b : F) ^ 2 - 4 * (c : F) := rfl
  refine ⟨2 * a + algebraMap (𝓞 F) (𝓞 E) b, b ^ 2 - 4 * c, ?_, ?_, ?_, ?_⟩
  · rw [hδ, map_add, map_mul, map_ofNat, AlgHom.commutes, hc]
    ring
  · rw [hδ, hD, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hq
  · intro h
    apply disc_sub_sq_notMem v b c 0 h2 hroot
    simpa using neg_mem h
  · simpa using disc_sub_sq_notMem v b c 1 h2 hroot

theorem exists_inv (v : Pl F) (D : 𝓞 F) (hD : D ∉ v.asIdeal) :
    ∃ c : Fv F v, c ∈ v.adicCompletionIntegers F ∧ c * algebraMap F (Fv F v) (D : F) = 1 := by
  have h1 : Valued.v (algebraMap F (Fv F v) (D : F)) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (D : F)
    have h' : v.valuation F (D : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hD
    rw [← h', ← h]
    rfl
  have h0 : algebraMap F (Fv F v) (D : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨(algebraMap F (Fv F v) (D : F))⁻¹, ?_, inv_mul_cancel₀ h0⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} (hz : At (evFin F v) z)
    {a : AF F} (ha : evFin F v a = 1) : a • z = z := by
  have h := hz (a - 1) (by rw [map_sub, map_one, ha, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero] at h

theorem at_of_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl F) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    At (evFin F v) z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    intro u hu
    rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]

theorem lift_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl F) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (o : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    (GlobalTheory.LatVac.liftV v c • inclR (F := F) (AF F) (o : E)) • z ∈ latAt W v :=
  GlobalTheory.InertLocFrame.Lat.smul_mem_latAt W (AddSubgroup.subset_closure
    ⟨_, GlobalTheory.LatVac.at_liftV v c, by rwa [GlobalTheory.LatVac.evFin_liftV], o, rfl⟩) hz

end GlobalTheory.InertSph.Scal

namespace GlobalTheory.InertSph

open GlobalTheory.InertSph.Scal GlobalTheory.LatVac in

theorem exists_traceZero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : AE F E, At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  intro F E _ _ _ _ _ σ B hB d W v w hin
  obtain ⟨δ, D, hσ, hsq, hD, hD1⟩ := exists_delta σ hB.cm v w hin (hB.inert v w hin).1
  obtain ⟨c, hc, hcD⟩ := exists_inv v D hD
  obtain ⟨c', hc', hcD'⟩ := exists_inv v (1 - D) hD1
  have hcD'' : c' * (1 - algebraMap F (Fv F v) (D : F)) = 1 := by
    rwa [show ((1 - D : 𝓞 F) : F) = 1 - (D : F) from rfl, map_sub, map_one] at hcD'
  set x : AE F E := inclR (F := F) (AF F) (δ : E) with hx
  have hxx : x * x = algebraMap (AF F) (AE F E) (algebraMap F (AF F) (D : F)) := by
    rw [hx, ← map_mul, hsq, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes _
  have hp : inclR (F := F) (AF F) ((1 + δ : 𝓞 E) : E) = 1 + x := by
    rw [show ((1 + δ : 𝓞 E) : E) = 1 + (δ : E) from rfl, map_add, map_one]
  have hm : inclR (F := F) (AF F) ((1 - δ : 𝓞 E) : E) = 1 - x := by
    rw [show ((1 - δ : 𝓞 E) : E) = 1 - (δ : E) from rfl, map_sub, map_one]
  have he : liftV v (1 : Fv F v) * liftV v c' = liftV v c' :=
    smul_eq_of_at (at_liftV v c') (evFin_liftV v 1)
  have he' : algebraMap (AF F) (AE F E) (liftV v (1 : Fv F v)) * algebraMap (AF F) (AE F E) (liftV v c') =
      algebraMap (AF F) (AE F E) (liftV v c') := by rw [← map_mul, he]
  have key : ∀ z ∈ latAt W v, ∀ a : AF F, evFin F v a = 1 → algebraMap (AF F) (AE F E) a • z = z := by
    intro z hz a ha
    rw [algebraMap_smul]
    exact smul_eq_of_at (at_of_mem_latAt W v hz) ha
  have hu : evFin F v (liftV v c' * (1 - algebraMap F (AF F) (D : F))) = 1 := by
    rw [map_mul, map_sub, map_one, evFin_liftV, AlgHom.commutes, hcD'']
  refine ⟨liftV v 1 • x, liftV v c • x, liftV v c' • (1 - x), liftV v c' • (1 + x), ?_, ?_, fun z hz =>
    ⟨lift_smul_mem W v (one_mem _) δ hz, lift_smul_mem W v hc δ hz, hm ▸ lift_smul_mem W v hc' (1 - δ) hz,
      hp ▸ lift_smul_mem W v hc' (1 + δ) hz, ?_, ?_, ?_⟩⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]
  · have h : cA σ x = -x := by
      have h1 : cA σ x = inclR (F := F) (AF F) (σ (δ : E)) := by
        simp [hx, cA, inclR]
      rw [h1, hσ, map_neg]
    rw [map_smul, h, smul_neg]
  · have h := key z hz (liftV v 1 * liftV v c * algebraMap F (AF F) (D : F)) (by
      rw [map_mul, map_mul, evFin_liftV, evFin_liftV, AlgHom.commutes, one_mul, hcD])
    convert h using 2
    simp only [Algebra.smul_def, map_mul, ← hxx]
    ring
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (x * (1 - x)) * he'
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (-x * (1 + x)) * he'

end GlobalTheory.InertSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeVectorOfGoodLevelRepresentation
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TypeVec

section Gen

theorem isIrreducible_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H' X) (f : H →* H') (hf : Function.Surjective f) (hτ : τ.IsIrreducible) :
    Representation.IsIrreducible (τ.comp f) := by
  let e : Subrepresentation (τ.comp f : Representation ℂ H X) ≃o Subrepresentation τ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).2 hτ

def glMap {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    GL (Fin n) K →* GL (Fin m) K' :=
  (Units.map (Matrix.reindexAlgEquiv K' K' (finCongr h.symm)).toAlgHom.toRingHom.toMonoidHom).comp
    (Matrix.GeneralLinearGroup.map e.toRingHom)

theorem glMap_apply {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin n) K) (i j : Fin m) : (glMap e h g).1 i j = e (g.1 (Fin.cast h i) (Fin.cast h j)) := rfl

theorem glMap_symm {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin m) K') : glMap e h (glMap e.symm h.symm g) = g := by
  apply Units.ext
  ext i j
  rw [glMap_apply, glMap_apply]
  simp

theorem glMap_surjective {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    Function.Surjective (glMap e h) := fun g => ⟨glMap e.symm h.symm g, glMap_symm e h g⟩

theorem mem_fixed_iff {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X}
    {K : Subgroup H} {x : X} : x ∈ GlobalTheory.PRep.fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp

end Gen

variable {D : D7}

def typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible) :
    TypeDataG V where
  S := S
  frame := s
  W := fun w => Fin (n (pl w)) → ℂ
  τ := fun w => (τ (pl w)).comp (glMap (ρv w) hr)
  irred := fun w => isIrreducible_comp _ _ (glMap_surjective _ _) (hτ (pl w))

theorem noFixed_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    (hne : S.Nonempty)
    (h : ∀ a, 0 < a → a < V.rank → ∃ v : S, ∀ y : Fin (n (pl v)) → ℂ,
      (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF v.1) V.rank a, τ (pl v) (glMap (ρv v) hr g) y = y) → y = 0) :
    NoFixed (typeOf hr S pl s ρv n τ hτ) :=
  ⟨hne, h⟩

theorem hasTypeVec_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W) (hx : x ≠ 0)
    (hoff : ∀ v ∉ S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x)
    (hon : ∀ v : S, x ∈ Submodule.span ℂ {y | ∃ φ : (Fin (n (pl v)) → ℂ) →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (τ (pl v) (glMap (ρv v) hr ((s v).red k)) z) = σ (locFin V v k) (φ z)) ∧
        y ∈ LinearMap.range φ}) :
    HasTypeVec (typeOf hr S pl s ρv n τ hτ) σ :=
  ⟨x, hx, hoff, hon⟩

set_option maxHeartbeats 1000000 in

theorem hasTypeVec_of_goodRep : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), IsAdmissible σ → GlobalTheory.CuspMult.IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ → ∃ T : TypeDataG (Yc D 0), NoFixed T ∧ HasTypeVec T σ := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F hF W _ _ σ _hadm hgood
  classical
  have hrk : (Yc D 0).rank = D.R.r := by rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hlev := hF.core.lev
  obtain ⟨c0, hbase⟩ := hlev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hnc : ∀ PP ∈ (R.dat0 R.triv).Pg, ∀ PP' ∈ (R.dat0 R.triv).Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP hP PP' hP'
    obtain ⟨k, hk⟩ := (hlev.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (hlev.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_finiteGroupAction_principalLevelFixedVectors D (Yc D 0) (R.βY 0) (R.dat0 R.triv) (GlobalTheory.ProjectedLift.liftsExist_rows R hlev) W σ
  obtain ⟨v, hv0, hvK, κ, hκ, hve⟩ := hgood
  have hvmem : v ∈ GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))) :=
    mem_fixed_iff.2 fun k => hvK _ (Subgroup.mem_subgroupOf.1 k.2)
  haveI : Finite (G0 R.Pg D.R.r) := Finite.of_equiv G R.eG.toEquiv
  have hfix : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • ρ (R.eG g) ⟨v, hvmem⟩ = ⟨v, hvmem⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hve
    rw [SetLike.val_smul, hρ (R.eG g) (κ g) (hκ g)]
  obtain ⟨U, hUfd, hUirr, y, hy0, hye⟩ := GlobalTheory.T.exists_irreducible_subrep_with_groupAlgebra_fixed _ _ _ ρ (fun g => R.eG g) _ ⟨v, hvmem⟩
    (fun h => hv0 (congrArg Subtype.val h)) hfix
  haveI := hUfd
  have hH := GlobalTheory.T.irreducible_not_killed_by_good_projector_satisfies_H hGC R F hF U.toSubmodule U.toRepresentation hUirr ⟨y, hy0, hye⟩
  choose n τ hτ hrest using GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups (↥R.Pg) (fun PP => GL (Fin D.R.r) (kP PP.1)) U.toSubmodule U.toRepresentation hUirr
  obtain ⟨a, S, pl, s, ρv, hoff, hon⟩ : ∃ (a : GfC (Yc D 0)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ R.Pg)
      (s : ∀ v : S, SplitAt D.sp.cm.sig (Yc D 0).gram (frameLat (Yc D 0)) v) (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1),
      (∀ v ∉ S, ∀ k ∈ Kv (Yc D 0) v, ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∈
        levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) ∧
      ∀ (v : S) (k : Kv (Yc D 0) v), ∃ g0 : G0 R.Pg D.R.r, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0
          ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∧
        (∀ PP, PP ≠ pl v → g0 PP = 1) ∧
        ∀ i j : Fin D.R.r, (g0 (pl v)).1 i j = ρv v (((s v).red k).1 (i.cast hrk.symm) (j.cast hrk.symm)) :=
    GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup D (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hrk.symm hbase rfl hnc

  let yW : W := (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)
  have hyK : ∀ h : ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))), σ h yW = yW := mem_fixed_iff.1 (y : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).2

  have hcomm : ∀ (l : GfC (Yc D 0)) (q : W), σ a⁻¹ (σ (a * l * a⁻¹) q) = σ l (σ a⁻¹ q) := by
    intro l q
    have e1 : σ a⁻¹ * σ (a * l * a⁻¹) = σ l * σ a⁻¹ := by
      rw [← map_mul, ← map_mul, show a⁻¹ * (a * l * a⁻¹) = l * a⁻¹ by group]
    exact congrArg (fun f : Module.End ℂ W => f q) e1
  have hconj : ∀ l : GfC (Yc D 0), σ (a * l * a⁻¹) yW = yW → σ l (σ a⁻¹ yW) = σ a⁻¹ yW :=
    fun l hl => (hcomm l yW).symm.trans (congrArg (σ a⁻¹) hl)
  refine ⟨typeOf hrk.symm S pl s ρv n τ hτ, noFixed_typeOf _ _ _ _ _ _ _ _ ?_ ?_,
    hasTypeVec_typeOf _ _ _ _ _ _ _ _ σ (σ a⁻¹ yW) ?_ ?_ ?_⟩
  · obtain ⟨PP, -⟩ := hH 1 one_pos (by omega)
    exact ⟨(pl.symm PP).1, (pl.symm PP).2⟩
  · intro b hb hbr
    obtain ⟨PP, hPP⟩ := hH b hb (lt_of_lt_of_eq hbr hrk)
    refine ⟨pl.symm PP, fun z hz => ?_⟩
    obtain ⟨⟨φ, hφi, hφ⟩, -⟩ := hrest (pl (pl.symm PP))
    have hpl : pl (pl.symm PP) = PP := pl.apply_symm_apply PP
    rw [← hpl] at hPP
    apply hφi
    refine Eq.trans ?_ (map_zero φ).symm
    apply hPP
    rintro u ⟨hu1, hu2⟩
    have e1 := hφ (u (pl (pl.symm PP))) z
    have hmem : glMap (ρv (pl.symm PP)).symm hrk (u (pl (pl.symm PP))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF (pl.symm PP).1) (Yc D 0).rank b := by
      intro i j hij
      rw [glMap_apply]
      have hent : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) =
          (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP (pl (pl.symm PP)).1)) (Fin.cast hrk i) (Fin.cast hrk j) := by
        by_contra hne
        exact hij (hu2 _ _ hne)
      by_cases hij' : i = j
      · subst hij'
        have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk i) = 1 := by simpa using hent
        simp only [h1, map_one, Matrix.one_apply_eq]
      · have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) = 0 := by
          rw [hent, Matrix.one_apply_ne (fun h => hij' (Fin.cast_injective hrk h))]
        simp only [h1, map_zero, Matrix.one_apply_ne hij']
    have h2 := hz _ hmem
    rw [glMap_symm] at h2
    refine Eq.trans ?_ (congrArg φ h2)
    refine Eq.trans ?_ e1.symm
    refine congrArg (fun g => U.toRepresentation g (φ z)) ?_
    funext P'
    by_cases h : P' = pl (pl.symm PP)
    · subst h
      exact (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).symm
    · exact (hu1 P' h).trans (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) h _).symm
  · intro h0
    apply hy0
    have h1 : yW = 0 := by
      have := congrArg (σ a) h0
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at this
    exact Subtype.ext (Subtype.ext h1)
  · intro w hw k hk
    exact hconj _ (hyK ⟨_, Subgroup.mem_subgroupOf.2 (hoff w hw k hk)⟩)
  · intro w
    obtain ⟨-, hsp⟩ := hrest (pl w)
    have hkey : ∀ (k : Kv (Yc D 0) w) (q : U.toSubmodule),
        σ a⁻¹ ((((U.toRepresentation (Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k))) q) :
          U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) =
          σ (locFin (Yc D 0) w k) (σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) := by
      intro k q
      have h2 := hon w k
      have hlift := h2.choose_spec.1
      have hone := h2.choose_spec.2.1
      have hent := h2.choose_spec.2.2
      have hg0 : Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k)) = h2.choose := by
        funext P'
        by_cases hP : P' = pl w
        · subst hP
          refine (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).trans ?_
          apply Units.ext
          ext i j
          exact (glMap_apply _ _ _ i j).trans (hent i j).symm
        · exact (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) hP _).trans (hone P' hP).symm
      have e2 := hρ _ (a * locFin (Yc D 0) w k * a⁻¹) hlift (q : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))))
      exact (congrArg (fun g => σ a⁻¹ ((((U.toRepresentation g q) : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) hg0).trans
        ((congrArg (σ a⁻¹) e2).trans (hcomm _ _))
    have hy := Submodule.eq_top_iff'.1 hsp y
    show σ a⁻¹ (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) ∈ _
    clear hconj hyK yW hye hy0
    induction hy using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨ψ, hψ, z, rfl⟩ := hu
      exact Submodule.subset_span ⟨(σ a⁻¹ ∘ₗ (GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).subtype ∘ₗ U.toSubmodule.subtype) ∘ₗ ψ,
        fun k z' => (congrArg (fun q : U.toSubmodule => σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W))
          (hψ _ z')).trans (hkey k (ψ z')), z, rfl⟩
    | zero => simpa using zero_mem _
    | add u u' _ _ hu hu' => simpa only [Submodule.coe_add, map_add] using add_mem hu hu'
    | smul c u _ hu => simpa only [Submodule.coe_smul, map_smul] using Submodule.smul_mem _ c hu

end GlobalTheory.TypeVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_crd_of_mem_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u hu
  obtain ⟨hC, b, hZ⟩ := (mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF u).1 hu
  set s := sigR (AF F) σ with hsdef
  set M := (matHom _ σ J u).1 with hMdef
  have hU : cT s M * adMat F J * M = adMat F J := u.2
  have hs : ∀ a : AF F ⊗[F] E, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hF.cm x)
  have cc : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (cT s X) = X :=
    fun X => Matrix.ext fun i k => hs _
  have cadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X + Y) = cT s X + cT s Y :=
    fun X Y => Matrix.ext fun i k => map_add s _ _
  have csub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X - Y) = cT s X - cT s Y :=
    fun X Y => Matrix.ext fun i k => map_sub s _ _
  have cad : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), cT s (adMat F X) = adMat F (cT (σ : E →+* E) X) :=
    fun X => GlobalTheory.AutFunCounterexample.cT_map_gen σ X
  have gram : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      cT s (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := fun X Y => by
    rw [cad]; simp only [adMat, Matrix.map_mul]
  have unit : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin b) (AF F ⊗[F] E)),
      cT s (M * X) * adMat F J * (M * Y) = cT s X * adMat F J * Y := fun X Y => by
    have e : cT s X * cT s M * adMat F J * (M * Y) = cT s X * (cT s M * adMat F J * M) * Y := by
      simp only [Matrix.mul_assoc]
    rw [Formalism.UG.cT_mul, e, hU]
  have ad0 : ∀ {a b : ℕ}, adMat F (0 : Matrix (Fin a) (Fin b) E) = 0 := fun {a b} => Matrix.map_zero _ (map_zero _)
  have ad1 : ∀ {a : ℕ}, adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := fun {a} => Matrix.map_one _ (map_zero _) (map_one _)

  have h1 : cT s (adMat F C) * adMat F J * (M * adMat F D) = 1 := by
    conv_lhs => rw [← hC]
    rw [unit, gram, hF.cd, ad1]
  have h2 : cT s (adMat F Z) * adMat F J * (M * adMat F D) = - cT s b := by
    have e := unit (adMat F Z) (adMat F D)
    rw [hZ, gram, hF.zd, ad0, cadd, Formalism.UG.cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (cT s b),
      Matrix.mul_assoc (cT s b), h1, Matrix.mul_one] at e
    exact eq_neg_of_add_eq_zero_left e
  set c := cT s (adMat F D) * adMat F J * (M * adMat F D) with hc
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J)) +
      adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have e := congrArg (fun X => adMat F X) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
    simp only [cad, adMat]
    exact e
  have hD : M * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
    conv_lhs => rw [← Matrix.one_mul (M * adMat F D), ← hsum]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F Z)),
      ← Matrix.mul_assoc (cT s (adMat F C)), h1, h2, Matrix.mul_one, plus, Matrix.mul_neg, Matrix.mul_neg, ← hc]
    abel
  refine ⟨b, c, ⟨hC, hZ, hD⟩, ?_⟩

  have h0 := unit (adMat F D) (adMat F D)
  rw [gram, hF.dd, ad0] at h0
  have hP : cT s (plus σ J₀ b) = b * adMat F J₀⁻¹ := by
    rw [plus, Formalism.UG.cT_mul, cc, cad, GlobalTheory.UAut.cT_form_inv hF.herm₀]
  conv_lhs at h0 => rw [hD]
  rw [cadd, csub, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hP, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (cT s c),
    Matrix.mul_assoc (cT s c), ← hD, h1, h2, ← hc, Matrix.mul_one] at h0
  rw [← h0, plus, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtensionStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilTransport_adelicSchwartz_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  first | exact @GlobalTheory.TransportF.exists_isTransportF | exact GlobalTheory.TransportF.exists_isTransportF | (intros; apply GlobalTheory.TransportF.exists_isTransportF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCompactInterUnitaryRationalPointsStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_compact_inter_unitaryRationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)), IsCompact K → (K ∩ ratPts σ J).Finite := by
  first | exact @GlobalTheory.SphEis.compact_inter_ratPts_finite | exact GlobalTheory.SphEis.compact_inter_ratPts_finite | (intros; apply GlobalTheory.SphEis.compact_inter_ratPts_finite <;> assumption)
end

