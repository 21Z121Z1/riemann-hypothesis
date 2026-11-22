import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0047
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0118
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0083
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FieldTwistConditions
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessTangentFamilyStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_tangent_family : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (m : ℕ) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (eig : (epsR (PowerSeries A) ⟶ W.t.G) → Prop), (∀ w, eig w ↔ ∀ x : 𝓞 E, (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ w.left) → (∀ k, LieImg W (e k) (v k)) → (∀ k, IsTangent (v k) ∧ eig (v k)) → ((∀ w, IsTangent w → eig w → ∃! cf : Fin m → PowerSeries A, IsLieComb cf v w) ↔ ∀ ν w, LieImg W ν w → IsTangent w → eig w → ∃! cf : Fin m → A, GtComb cf e ν) := by
  first | exact @GlobalTheory.ConstEig.basis_iff_const | exact GlobalTheory.ConstEig.basis_iff_const | (intros; apply GlobalTheory.ConstEig.basis_iff_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

theorem exists_gaussRing_map :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (σ : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Op X la N) ∧ (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧ (∀ o, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la o) = algebraMap (Op X la N) (Kp X la N) (f o)) ∧ (∀ a : B.KO, φ (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ q, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (σ q)) := by
  intro D B P j X la N D' N' σ
  obtain ⟨f, φ, h1, h2, h3, h4, h5, h6, h7⟩ := gaussRing_completion_rename D B P j X la N D' N' σ
  refine ⟨f, φ, h1, h2, h3, h4, h5, fun a => ?_, h7⟩
  rw [IsScalarTower.algebraMap_apply B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
    (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'), MvPolynomial.algebraMap_eq]
  exact h6 a

end GlobalTheory.GaussCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsometryAgreeing
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfLift

theorem exists_isometry_agreeing {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (l : Level H) (g g' : Dw.La →ₗ[𝓞 E] Dw.La)
    (h : ∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ s : Sim Dw, (∀ n, s.ν n = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), Dw.ModN l.M (s.f l.M a - g a) := by
  have hle : ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤
      (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).comap f := fun f => by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  obtain ⟨s, h1, h2, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing E H Dw l
    (LinearEquiv.ofLinear (Submodule.mapQ _ _ g (hle g)) (Submodule.mapQ _ _ g' (hle g'))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).2))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).1)))
  refine ⟨s, h1, fun a ha => ?_⟩
  have key : ∀ x, s.f l.M x - g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun x =>
    (Submodule.Quotient.eq _).1 (h2 x)
  refine Submodule.smul_induction_on ha (fun r hr y _ => ?_) fun y z hy hz => ?_
  · rw [map_smul, map_smul, ← smul_sub]
    exact GlobalTheory.LevelIsometry.modN_smul_of_mem_smul Dw l hr (key y)
  · rw [map_add, map_add, add_sub_add_comm]
    exact GlobalTheory.SimAlg.modN_add hy hz

theorem add_sub_eq_nsmul {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) :
    x + N • e + N • w - x = N • (e + w) := by
  rw [smul_add]
  abel

theorem exists_unitary_inducing : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V ι → ∀ g g' : Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ∧ g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ∃ u ∈ GfC V, gLat V u = latHat V ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1, (finHom V u).1.mulVec (finVec V (ι a)) - finVec V (ι (g a)) = (l.M : ℕ) • w := by
  intro D H Dw l V ι hι g g' h
  obtain ⟨s, hν, hs⟩ := exists_isometry_agreeing Dw l g g' h
  obtain ⟨κ, hκ, hκs⟩ := GlobalTheory.ShortMove.exists_adelic_of_isometry D V H Dw ι hι.emb hι.isom s hν
  obtain ⟨b, hb, u, hu, e⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
  have hb' : finHom V b = 1 := hb
  have hf : finHom V u = finHom V κ := by rw [e, map_mul, hb', one_mul]
  obtain ⟨-, m2, -, m4⟩ := GlobalTheory.Member.latG_move D V
  have hL : latG V 1 = latG V u := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V (hκ.symm.trans (m2 u κ hf).2.symm)
  have hc := m4 1 u hL
  rw [inv_one, one_mul] at hc
  refine ⟨u, hu, GlobalTheory.MarkDet.gLat_eq_of_finCong hc, fun a ha => ?_⟩
  obtain ⟨c, hc'⟩ := hs a ha
  obtain ⟨w, hw, ew⟩ := hκs l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
  have hm : finVec V (ι c) ∈ latGHat V 1 :=
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.emb.2 ▸ LinearMap.mem_range_self ι c)
  refine ⟨finVec V (ι c) + w, add_mem hm hw, ?_⟩
  have h2 : finVec V (ι (s.f l.M a)) = finVec V (ι (g a)) + l.M • finVec V (ι c) := by
    rw [sub_eq_iff_eq_add'.1 hc', map_add, map_nsmul]
    funext i
    simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
    congr 1
    exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _
  rw [hf, ew, h2]
  exact add_sub_eq_nsmul _ _ _ _

end GlobalTheory.HalfLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsXiOKNotTwistCond
section
noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

variable {D : D7}

def Reformulated (D : D7) (p : ℕ) : Prop := p = D.host.pde ∨ p = D.host.pde'

theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

theorem barF_tmul (a : Af D.host.F) (e : D.host.E) :
    barF D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] D.host.conj e := by
  rw [← cF_eq]; rfl

theorem bar_eq (x : AfE D) : FieldTwistConditions.bar D x = barF D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [barF_tmul, ← D.conjF_eq]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem normOne_iff (x : (AfE D)ˣ) : FieldTwistConditions.NormOne D x ↔ NormOne x := by
  unfold FieldTwistConditions.NormOne NormOne
  rw [bar_eq]

def UnramOff (D : D7) (p : ℕ) (xi : (AfE D)ˣ →* ℂˣ) : Prop := ∀ x, NormOne x → CongOne p x → xi x = 1

def OrderFifteen (D : D7) (p : ℕ) (xi : (AfE D)ˣ →* ℂˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ n : ℕ, (∀ u, FieldTwistConditions.InertiaAt D v u → xi u ^ n = 1) ↔ 15 ∣ n

end GlobalTheory.TwistFieldCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def onePlusCas (σ : Mx n → (H →L[ℂ] H)) {d : ℕ} (X : Fin d → Mx n) (v : H) : H :=
  v - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) : Sm ε σ (onePlusCas σ X v) := by
  have h1 : ∀ i, Sm ε σ (dRep σ (X i) (dRep σ (X i) v)) := fun i =>
    dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv (hX i)) (hX i)
  exact (smooth (Jm ε) σ).sub_mem hv ((smooth (Jm ε) σ).sum_mem fun i _ => h1 i)

theorem sm_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) (r : ℕ) : Sm ε σ ((onePlusCas σ X)^[r] v) := by
  induction r with
  | zero => simpa using hv
  | succ r ih => rw [Function.iterate_succ_apply']; exact sm_onePlusCas hσ hX ih

theorem inner_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, onePlusCas σ X v⟫_ℂ = ⟪onePlusCas σ X b, v⟫_ℂ := by
  have key : ∀ i, ⟪b, dRep σ (X i) (dRep σ (X i) v)⟫_ℂ = ⟪dRep σ (X i) (dRep σ (X i) b), v⟫_ℂ := fun i => by
    have hv1 := dRep_mem (isUnit_Jm ε) hσ hv (hX i)
    have hb1 := dRep_mem (isUnit_Jm ε) hσ hb (hX i)
    rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 (hX i), inner_dRep (isUnit_Jm ε) hσ hb1 hv (hX i), neg_neg]
  simp only [onePlusCas, inner_sub_left, inner_sub_right, inner_sum, sum_inner, key]

theorem inner_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) (r : ℕ) :
    ⟪b, (onePlusCas σ X)^[r] v⟫_ℂ = ⟪(onePlusCas σ X)^[r] b, v⟫_ℂ := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih (sm_onePlusCas hσ hX hv), Function.iterate_succ_apply',
      inner_onePlusCas hσ hX (sm_iterate_onePlusCas hσ hX hb r) hv]

theorem onePlusCas_smul (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    (c : ℂ) {v : H} (hv : Sm ε σ v) : onePlusCas σ X (c • v) = c • onePlusCas σ X v := by
  have h : ∀ i, dRep σ (X i) (dRep σ (X i) (c • v)) = c • dRep σ (X i) (dRep σ (X i) v) := fun i =>
    Dw_smul hσ (l := [X i, X i]) (by simp [hX i]) c hv
  simp only [onePlusCas, h, smul_sub, Finset.smul_sum]

theorem iterate_onePlusCas_of_eq (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {v : H} (hv : Sm ε σ v) {μ : ℂ} (h : onePlusCas σ X v = μ • v) (r : ℕ) :
    (onePlusCas σ X)^[r] v = μ ^ r • v := by
  induction r with
  | zero => simp
  | succ r ih => rw [Function.iterate_succ_apply', ih, onePlusCas_smul hσ hX _ hv, h, smul_smul, pow_succ]

end GlobalTheory.TypeSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace GlobalTheory.TypeSum.CoefClos

variable {n : ℕ}

abbrev Ltr (ε : Fin n → Bool) : Type := {X : Mx n // X ∈ lieSet ε} ⊕ {k : Mx n // k ∈ Kset ε}

section Vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ltrV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} : Ltr ε → H → H
  | Sum.inl X => dRep σ X.1
  | Sum.inr k => σ k.1

def wordV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} (u : List (Ltr ε)) (v : H) : H := u.foldr (ltrV σ) v

end Vec

def rder (X : Mx n) (f : Mx n → ℂ) (g : Mx n) : ℂ := deriv (fun t : ℝ => f (g * NormedSpace.exp (t • X))) 0

def ltrF {ε : Fin n → Bool} : Ltr ε → (Mx n → ℂ) → Mx n → ℂ
  | Sum.inl X => rder X.1
  | Sum.inr k => fun f g => f (g * k.1)

def wordF {ε : Fin n → Bool} (u : List (Ltr ε)) (f : Mx n → ℂ) : Mx n → ℂ := u.foldr ltrF f

def wordE {M : Type} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool} (τ : Ltr ε → Module.End ℂ M)
    (u : List (Ltr ε)) (m : M) : M := u.foldr (fun x => τ x) m

def CSm (ε : Fin n → Bool) (f : Mx n → ℂ) : Prop :=
  ∃ F : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, F [] g = f g) ∧ IsDerFam ε F ∧
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)

variable {ε : Fin n → Bool}

theorem CSm.congr {f f' : Mx n → ℂ} (h : CSm ε f) (e : ∀ g ∈ UJset ε, f g = f' g) : CSm ε f' := by
  obtain ⟨F, h1, h2, h3⟩ := h
  exact ⟨F, fun g hg => (h1 g hg).trans (e g hg), h2, h3⟩

theorem CSm.add {f f' : Mx n → ℂ} (h : CSm ε f) (h' : CSm ε f') : CSm ε (f + f') := by
  obtain ⟨F, h1, h2, h3⟩ := h
  obtain ⟨F', k1, k2, k3⟩ := h'
  refine ⟨fun l g => F l g + F' l g, fun g hg => by simp [h1 g hg, k1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => (h3 l hl).add (k3 l hl)⟩
  exact (h2 l hl X hX g hg).add (k2 l hl X hX g hg)

theorem CSm.smul {f : Mx n → ℂ} (h : CSm ε f) (c : ℂ) : CSm ε (c • f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l g => c * F l g, fun g hg => by simp [h1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => continuousOn_const.mul (h3 l hl)⟩
  exact (h2 l hl X hX g hg).const_mul c

theorem CSm.zero : CSm ε (0 : Mx n → ℂ) :=
  ⟨fun _ _ => 0, fun _ _ => rfl, fun _ _ _ _ _ _ => hasDerivAt_const _ _, fun _ _ => continuousOn_const⟩

theorem CSm.sum {ι : Type} (s : Finset ι) {f : ι → Mx n → ℂ} (h : ∀ i ∈ s, CSm ε (f i)) :
    CSm ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CSm.zero (ε := ε))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CSm.hasDerivAt {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (rder X f g) 0 := by
  obtain ⟨F, h1, h2, -⟩ := h
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rwa [rder, h0.deriv]

theorem CSm.rder_eq {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ} (h1 : ∀ g ∈ UJset ε, F [] g = f g)
    (h2 : IsDerFam ε F) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) : rder X f g = F [X] g := by
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rw [rder, h0.deriv]

theorem CSm.rder {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) : CSm ε (rder X f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l => F (l ++ [X]), fun g hg => (CSm.rder_eq h1 h2 hX hg).symm, fun l hl Y hY g hg => ?_,
    fun l hl => h3 _ ?_⟩
  · exact h2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
  · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)

theorem exp_conj_smul {k : Mx n} (hk : k ∈ UJset ε) (Y : Mx n) (t : ℝ) :
    k⁻¹ * NormedSpace.exp (t • Y) * k = NormedSpace.exp (t • (k⁻¹ * Y * k)) := by
  have hu : IsUnit k⁻¹ := (isUnit_of_UJ (inv_mem_UJ hk))
  have e := Matrix.exp_conj k⁻¹ (t • Y) hu
  rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hk))] at e
  rw [← e, Matrix.mul_smul, Matrix.smul_mul]

theorem CSm.rt {f : Mx n → ℂ} (h : CSm ε f) {k : Mx n} (hk : k ∈ Kset ε) : CSm ε (fun g => f (g * k)) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  have hkU := K_le_UJ hk
  refine ⟨fun l g => F (l.map fun Y => k⁻¹ * Y * k) (g * k), fun g hg => by simpa using h1 _ (mul_mem_UJ hg hkU),
    fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    have hY' : k⁻¹ * Y * k ∈ lieSet ε := conj_mem_lie (isUnit_Jm ε) hkU hY
    have := h2 _ hl' _ hY' (g * k) (mul_mem_UJ hg hkU)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ (g * NormedSpace.exp (t • Y) * k) = F _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
    rw [← exp_conj_smul hkU Y t]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    exact (h3 _ hl').comp (continuous_id.mul continuous_const).continuousOn fun g hg => mul_mem_UJ hg hkU

theorem CSm.ltrF {f : Mx n → ℂ} (h : CSm ε f) (x : Ltr ε) : CSm ε (ltrF x f) := by
  rcases x with X | k
  · exact h.rder X.2
  · exact h.rt k.2

theorem CSm.wordF {f : Mx n → ℂ} (h : CSm ε f) (u : List (Ltr ε)) : CSm ε (wordF u f) := by
  induction u with
  | nil => exact h
  | cons x u ih => exact ih.ltrF x

def Smo (ε : Fin n → Bool) : Submodule ℂ (Mx n → ℂ) where
  carrier := {f | (∀ g ∉ UJset ε, f g = 0) ∧ CSm ε f}
  add_mem' := fun {f f'} hf hf' => ⟨fun g hg => by simp [hf.1 g hg, hf'.1 g hg], hf.2.add hf'.2⟩
  zero_mem' := ⟨fun _ _ => rfl, CSm.zero⟩
  smul_mem' := fun c f hf => ⟨fun g hg => by simp [hf.1 g hg], hf.2.smul c⟩

theorem not_mem_of_mul_exp {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∉ UJset ε) (t : ℝ) :
    g * NormedSpace.exp (t • X) ∉ UJset ε := by
  intro h
  apply hg
  have := mul_mem_UJ h (exp_mem_UJ hX (-t))
  rwa [Matrix.mul_assoc, ← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this

theorem rder_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n}
    (hg : g ∉ UJset ε) : rder X f g = 0 := by
  have : (fun t : ℝ => f (g * NormedSpace.exp (t • X))) = fun _ => 0 :=
    funext fun t => hf _ (not_mem_of_mul_exp hX hg t)
  rw [rder, this, deriv_const]

theorem rt_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {k : Mx n} (hk : k ∈ Kset ε) {g : Mx n}
    (hg : g ∉ UJset ε) : f (g * k) = 0 := by
  refine hf _ fun h => hg ?_
  have := mul_mem_UJ h (inv_mem_UJ (K_le_UJ hk))
  rwa [Matrix.mul_assoc, mul_inv_UJ (K_le_UJ hk), Matrix.mul_one] at this

theorem ltrF_mem {f : Mx n → ℂ} (hf : f ∈ Smo ε) (x : Ltr ε) : ltrF x f ∈ Smo ε := by
  refine ⟨fun g hg => ?_, hf.2.ltrF x⟩
  rcases x with X | k
  · exact rder_off hf.1 X.2 hg
  · exact rt_off hf.1 k.2 hg

theorem rder_add {f f' : Mx n → ℂ} (hf : f ∈ Smo ε) (hf' : f' ∈ Smo ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (f + f') = rder X f + rder X f' := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).add (hf'.2.hasDerivAt hX hg)).deriv
  · simp [rder_off (Submodule.add_mem _ hf hf').1 hX hg, rder_off hf.1 hX hg, rder_off hf'.1 hX hg]

theorem rder_smul {f : Mx n → ℂ} (hf : f ∈ Smo ε) (c : ℂ) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (c • f) = c • rder X f := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).const_mul c).deriv
  · simp [rder_off (Submodule.smul_mem _ c hf).1 hX hg, rder_off hf.1 hX hg]

def ltrM (x : Ltr ε) : Module.End ℂ (Smo ε) where
  toFun f := ⟨ltrF x f.1, ltrF_mem f.2 x⟩
  map_add' f f' := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_add f.2 f'.2 X.2
    · rfl
  map_smul' c f := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_smul f.2 c X.2
    · rfl

theorem coe_wordE (u : List (Ltr ε)) (f : Smo ε) : ((wordE ltrM u f : Smo ε) : Mx n → ℂ) = wordF u f := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show ltrF x (wordE ltrM u f : Smo ε).1 = ltrF x (wordF u f.1)
    rw [ih]

theorem wordF_congr {f f' : Mx n → ℂ} (e : ∀ g ∈ UJset ε, f g = f' g) (u : List (Ltr ε)) :
    ∀ g ∈ UJset ε, wordF u f g = wordF u f' g := by
  induction u with
  | nil => exact e
  | cons x u ih =>
    intro g hg
    rcases x with X | k
    · show deriv _ 0 = deriv _ 0
      congr 1
      funext t
      exact ih _ (mul_mem_UJ hg (exp_mem_UJ X.2 t))
    · exact ih _ (mul_mem_UJ hg (K_le_UJ k.2))

end GlobalTheory.TypeSum.CoefClos

end
end

