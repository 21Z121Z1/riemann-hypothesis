import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0015
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEWeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 4000000 in

theorem map_transpose_inv {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) {r : ℕ} (T : Matrix (Fin r) (Fin r) Ω)
    (hT : IsUnit T.det) : (Tᵀ⁻¹).map i = (T.map i)ᵀ⁻¹ := by
  have h1 : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.transpose_map, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ h1, Matrix.map_one _ (map_zero i) (map_one i)]

set_option maxHeartbeats 4000000 in

theorem isUnit_det_rev {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (hM : IsUnit M.det) :
    IsUnit (Matrix.of fun a b => M a (Fin.rev b)).det := by
  have e : (Matrix.of fun a b => M a (Fin.rev b)) = M.submatrix id (Fin.revPerm : Equiv.Perm (Fin r)) := by
    ext a b; rfl
  rw [e, Matrix.det_permute']
  exact IsUnit.mul ((Units.isUnit _).map (Int.castRingHom R)) hM

set_option maxHeartbeats 4000000 in

theorem isFrameAt_of_map {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] {L : Lat ξ E} {f : E →ₗ[Ω] E'}
    (hf : Function.Injective f) {r : ℕ} {b : Fin r → E} {p : Cpt ξ}
    (h : (L.map f).IsFrameAt (fun a => f (b a)) p) : L.IsFrameAt b p := by
  unfold Lat.IsFrameAt at h ⊢
  unfold Lat.map at h
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have e2 : Submodule.map (f.restrictScalars (regAt ξ p)) (Submodule.span (regAt ξ p) (Set.range b)) =
      Submodule.span (regAt ξ p) (Set.range fun a => f (b a)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    simp
  exact Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ p)) hf (h.2.trans e2.symm)

set_option maxHeartbeats 4000000 in

theorem forms_quotient {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) (R₀ : Subring Ω) (R : Subring Φ)
    (hi : ∀ a ∈ R₀, i a ∈ R) {n r : ℕ} (A : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω)
    (C₀ : Matrix (Fin r) (Fin n) Ω) (t : Ω) (u U R₂ R₂' : Matrix (Fin r) (Fin r) Φ)
    (hreg : ∀ a b, (A * T) a b / t ∈ R₀) (hC₀ : ∀ a b, C₀ a b ∈ R₀)
    (hinv : ∀ a b, ∑ k, C₀ a k * ((A * T) k b / t) = if a = b then 1 else 0)
    (h2 : ∀ a b, R₂ a b ∈ R) (h2' : ∀ a b, R₂' a b ∈ R) (h1 : R₂ * R₂' = 1) (hu : u * U = T.map i * R₂) :
    ∃ C : Matrix (Fin r) (Fin n) Φ, (∀ a b, (A.map i * u * U) a b / i t ∈ R) ∧ (∀ a b, C a b ∈ R) ∧
      ∀ a b, ∑ k, C a k * ((A.map i * u * U) k b / i t) = if a = b then 1 else 0 := by
  classical
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Matrix (Fin n) (Fin r) Ω, Y₀ = Matrix.of fun k b => (A * T) k b / t := ⟨_, rfl⟩
  have hCY : C₀ * Y₀ = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, hY₀]
    exact hinv a b
  have hX : ∀ a b, (A.map i * u * U) a b / i t = (Y₀.map i * R₂) a b := by
    intro a b
    rw [Matrix.mul_assoc, hu, ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.map_apply, Matrix.map_apply, hY₀, Matrix.of_apply, map_div₀, div_mul_eq_mul_div]
  have hR : R₂' * R₂ = 1 := by
    rw [← Matrix.inv_eq_right_inv h1]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)
  refine ⟨R₂' * C₀.map i, ?_, ?_, ?_⟩
  · intro a b
    rw [hX, Matrix.mul_apply]
    refine R.sum_mem fun k _ => R.mul_mem ?_ (h2 k b)
    rw [Matrix.map_apply, hY₀, Matrix.of_apply]
    exact hi _ (hreg a k)
  · intro a b
    rw [Matrix.mul_apply]
    exact R.sum_mem fun k _ => R.mul_mem (h2' a k) (hi _ (hC₀ k b))
  · intro a b
    simp_rw [hX]
    have e : (R₂' * C₀.map i) * (Y₀.map i * R₂) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C₀.map i), ← Matrix.map_mul, hCY,
        Matrix.map_one _ (map_zero i) (map_one i), Matrix.one_mul, hR]
    have e2 := congrFun (congrFun e a) b
    rwa [Matrix.mul_apply, Matrix.one_apply] at e2

set_option maxHeartbeats 4000000 in
private theorem linearIndependent_of_dual_pairing {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] {r : ℕ}
    (B : Fin r → Module.Dual Ω W) (v : Fin r → W) (hBv : ∀ a b, B a (v b) = if a = b then 1 else 0) :
    LinearIndependent Ω v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h1 := congrArg (B a) hg
  simp only [map_sum, map_smul, hBv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, map_zero] at h1
  exact h1

set_option maxHeartbeats 4000000 in
private theorem isFrameAt_of_dual_basis {X : Scheme.{0}} {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W]
    [FiniteDimensional Ω W] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ W) (p : Cpt ξ) {r : ℕ}
    (hr : Module.finrank Ω W = r)
    (hmem : ∀ e : W, e ∈ L p ↔ ∀ w ∈ L.dual p, w e ∈ regAt ξ p)
    (B : Fin r → Module.Dual Ω W) (hB : L.dual p = Submodule.span (regAt ξ p) (Set.range B))
    (v : Fin r → W) (hBv : ∀ a b, B a (v b) = if a = b then 1 else 0) : L.IsFrameAt v p := by
  classical
  have hli := linearIndependent_of_dual_pairing B v hBv
  have hBmem : ∀ a, B a ∈ L.dual p := fun a => by rw [hB]; exact Submodule.subset_span ⟨a, rfl⟩
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · intro e he
    have hc : ∀ a, B a e ∈ regAt ξ p := fun a => (hmem e).1 he _ (hBmem a)
    have htop : Submodule.span Ω (Set.range v) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin, hr])
    obtain ⟨bv, hbv⟩ : ∃ bv : Module.Basis (Fin r) Ω W, ⇑bv = v :=
      ⟨Module.Basis.mk hli htop.ge, Module.Basis.coe_mk _ _⟩
    have hs := bv.sum_repr e
    rw [hbv] at hs
    have hco : ∀ b, bv.repr e b = B b e := by
      intro b
      conv_rhs => rw [← hs]
      simp only [map_sum, map_smul, hBv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [← hs]
    refine Submodule.sum_mem _ fun b _ => ?_
    have e1 : bv.repr e b • v b = (⟨B b e, hc b⟩ : regAt ξ p) • v b := by rw [hco]; rfl
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    refine (hmem (v b)).2 fun w hw => ?_
    rw [hB] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [hBv]
      split_ifs
      · exact (regAt ξ p).one_mem
      · exact (regAt ξ p).zero_mem
    | zero => rw [LinearMap.zero_apply]; exact (regAt ξ p).zero_mem
    | add x y _ _ hx hy => rw [LinearMap.add_apply]; exact (regAt ξ p).add_mem hx hy
    | smul a x _ hx => rw [LinearMap.smul_apply]; exact (regAt ξ p).mul_mem a.2 hx

set_option maxHeartbeats 4000000 in

theorem adapted_frame_om : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (rk (CMType H) D.p D.q (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (n (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ))) = if a = b then 1 else 0) ∧ ∀ l : Fin D.q, ((𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) l.rev).IsGenAt p' (U l l)⁻¹ := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hI
  unfold FormsOK at hF
  unfold HodgeOver at hO
  unfold ColFlags at hC
  obtain ⟨hd, -, -, hj, -⟩ := hO
  obtain ⟨T, C₀, hT, hfr, hreg, hC₀, hinv⟩ := GlobalTheory.T.exists_local_twist_trivialization 𝔐.X Ω 𝔐.ξ (EE 𝔐) (∀ k, J₀ k) (seg x₀)
    (LL 𝔐 (.inr τ)) (m (.inr τ)) _ (n (.inr τ)) (VV 𝔐 (.inr τ)) (φ (.inr τ)) (cc 𝔐 bW bO (.inr τ))
    (hF.2.2.1 _) (hF.1 _) (hF.2.1 _).1 (hF.2.1 _).2 ⟨pr p'.1, hp⟩ c₁ hI
  have e1 : colFrame (cc 𝔐 bW bO (.inr τ)) T = fun a => inO 𝔐 τ (colFrame (bO τ) T a) := by
    funext a
    simp only [colFrame, cc, map_sum, map_smul]
    rfl
  rw [e1] at hfr
  have hom : (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) T) ⟨pr p'.1, hp⟩ :=
    isFrameAt_of_map (GenBases.inO_injective 𝔐 τ) hfr
  have hvb := 𝔐.vb (.inr τ)
  obtain ⟨hcVB, hcmap⟩ := Lat.restrict_isVBOn _ _ _ _ _ _ _ _ hvb
  have hbid := (Lat.isVBOn_dual_and_bidual _ _ _ _ _ _ _ hcVB).2 ⟨pr p'.1, hp⟩ (Set.mem_univ _)
  obtain ⟨U', hpU, b₀, hb₀span, hb₀fr⟩ := hcVB ⟨pr p'.1, hp⟩ (Set.mem_univ _)
  have hb₀ := (hb₀fr ⟨pr p'.1, hp⟩ (Set.mem_univ _) hpU).1
  have : FiniteDimensional Ω (𝔐.Vgen (.inr τ)) := Module.Finite.of_basis (Module.Basis.mk hb₀ hb₀span.ge)
  have hrank : Module.finrank Ω (𝔐.Vgen (.inr τ)) = D.q := by
    rw [← Subspace.dual_finrank_eq, Module.finrank_eq_card_basis (bO τ), Fintype.card_fin]
  obtain ⟨v, hv⟩ : ∃ v : Fin (rk (CMType H) D.p D.q (.inr τ)) → 𝔐.Vgen (.inr τ), ∀ a b : Fin (rk (CMType H) D.p D.q (.inr τ)), bO τ a (v b) = if a = b then 1 else 0 := by
    refine ⟨fun b => (Module.evalEquiv Ω _).symm ((bO τ).dualBasis b), fun a b => ?_⟩
    simp only [Module.apply_evalEquiv_symm_apply]
    exact (bO τ).dualBasis_apply_self b a
  have hTt : IsUnit Tᵀ.det := by rwa [Matrix.det_transpose]
  have hBv : ∀ a b : Fin (rk (CMType H) D.p D.q (.inr τ)), colFrame (r := rk (CMType H) D.p D.q (.inr τ)) (bO τ) T a (colFrame v Tᵀ⁻¹ b) = if a = b then 1 else 0 := by
    intro a b
    have hm := congrFun (congrFun (Matrix.mul_nonsing_inv _ hTt) a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at hm
    rw [← hm]
    simp only [colFrame, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hv, smul_eq_mul,
      Matrix.transpose_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    try exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hLc := isFrameAt_of_dual_basis ((𝔐.V (.inr τ)).comap (𝔐.Vgen (.inr τ)).subtype) ⟨pr p'.1, hp⟩ hrank hbid
    (colFrame (bO τ) T) hom.2 (colFrame v Tᵀ⁻¹) hBv
  have hVfr : (𝔐.V (.inr τ)).IsFrameAt (fun k => ((colFrame v Tᵀ⁻¹ k : 𝔐.Vgen (.inr τ)) : 𝔐.Li))
      ⟨pr p'.1, hp⟩ := by
    refine ⟨hLc.1.map' _ (Submodule.ker_subtype _), ?_⟩
    have hc2 : ((𝔐.V (.inr τ)).comap (𝔐.Vgen (.inr τ)).subtype).map (𝔐.Vgen (.inr τ)).subtype ⟨pr p'.1, hp⟩ =
        𝔐.V (.inr τ) ⟨pr p'.1, hp⟩ := hcmap _ (Set.mem_univ _)
    rw [← hc2]
    unfold Lat.map
    rw [hLc.2, Submodule.map_span]
    congr 1
    ext x
    simp
    exact Iff.rfl
  have hpull := FlagPull.pull_isFrameAt hd hj p' hp hVfr
  rw [← hV (.inr τ)] at hpull
  have hcol : (fun k => j ((colFrame v Tᵀ⁻¹ k : 𝔐.Vgen (.inr τ)) : 𝔐.Li)) =
      colFrame (fun a => j (v a : 𝔐.Li)) ((Tᵀ⁻¹).map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))) := by
    funext k
    simp only [colFrame, Submodule.coe_sum, Submodule.coe_smul, map_sum, hj.1, Matrix.map_apply]
  rw [hcol, map_transpose_inv _ T hT] at hpull
  have hgdet : IsUnit (Matrix.of fun a b => (genU Ω (rk (CMType H) D.p D.q) (.inr τ))ᵀ⁻¹ a (Fin.rev b)).det := by
    apply isUnit_det_rev
    apply Matrix.isUnit_nonsing_inv_det
    rw [Matrix.det_transpose, DetG.det_genU]
    exact isUnit_one
  have hFl : Fl.b (.inr τ) = colFrame (fun a => j (v a : 𝔐.Li))
      (Matrix.of fun a b => (genU Ω (rk (CMType H) D.p D.q) (.inr τ))ᵀ⁻¹ a (Fin.rev b)) := by
    funext k
    rw [hC.2 τ v hv k, DetG.omBlock_gMat]
    rfl
  have hw : LinearIndependent (GenField Ω (rk (CMType H) D.p D.q)) (fun a => j (v a : 𝔐.Li)) :=
    hj.2 _ (fun a => (v a : 𝔐.Li)) ((linearIndependent_of_dual_pairing _ v hv).map' _ (Submodule.ker_subtype _))
  have hsub : (𝔐'.V (.inr τ)).IsFlagVBOn Set.univ (colFrame (fun a => j (v a : 𝔐.Li))
      (Matrix.of fun a b => (genU Ω (rk (CMType H) D.p D.q) (.inr τ))ᵀ⁻¹ a (Fin.rev b))) := by
    rw [← hFl]
    exact Fl.sub (.inr τ)
  obtain ⟨U₀, Rm, Rm', hU₀, hRm, hRm', hRR, hgU, hgr⟩ :=
    GlobalTheory.T.exists_triangular_regular_frame_change 𝔐'.X _ 𝔐'.ξ 𝔐'.Li (𝔐'.V (.inr τ)) _ (fun a => j (v a : 𝔐.Li)) _ _ p' hw hgdet hpull hsub
  have hTi : IsUnit (T.map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))).det := by
    have h := hT.map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))
    rw [RingHom.map_det] at h
    exact h
  obtain ⟨U₂, R₂, R₂', hU₂, hU₂d, hR₂, hR₂', hRR₂, hu⟩ :=
    GlobalTheory.T.exists_reversed_triangular_frame_change _ (regAt 𝔐'.ξ p') _ (genU Ω (rk (CMType H) D.p D.q) (.inr τ)) _ U₀ Rm Rm'
      (by rw [DetG.det_genU]; exact isUnit_one) hTi hU₀ (fun l => (hgr l).1) hRm hRm' hRR hgU
  obtain ⟨C, hC1, hC2, hC3⟩ := forms_quotient (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))
    (regAt 𝔐.ξ ⟨pr p'.1, hp⟩) (regAt 𝔐'.ξ p') (fun a ha => LatModel.dominates_regAt hd p' hp ha)
    (aOf 𝔐 bW bO φ (.inr τ)) T C₀ (seg x₀ c₁ ^ m (.inr τ)) _ U₂ R₂ R₂' hreg hC₀ hinv hR₂ hR₂' hRR₂ hu
  refine ⟨U₂, C, hU₂, hC1, hC2, hC3, fun l => ?_⟩
  rw [hU₂d l, inv_inv, hFl]
  exact hgr l.rev

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBoundStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_vertical_perturbation_bound : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L : Fin D → HermLine ι) (A B : HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → VertClose P T α A B → (∀ p ∈ T, ∀ j, NefAt P p (L j).a) → |II K ι P (D + 1) (Fin.snoc L A) - II K ι P (D + 1) (Fin.snoc L B)| ≤ (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) fun _ => 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines | exact GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamAlgebraicIndependentFinrank
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem genFam_degree_over_subfield : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_degree

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamRevInvSubfamily
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem isGenFam_revInv_ite : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_revgen

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsSectionDiagSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isSection_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsSection RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  refine ⟨fun x => ?_, fun x x' w hw => ?_⟩
  · obtain ⟨⟨F, H, hC⟩, -, -, hsrc, -, hu, -⟩ := hL x
    intro l z hz
    have hz' : z ∈ (RW.A.chart l).target ∩ (RW.A.chart l).symm ⁻¹' (ψ x).source :=
      ⟨hz.1, hsrc hz.2⟩
    have h1 : AnalyticAt ℂ (u x ∘ (RW.A.chart l).symm) z := hu l z hz
    have h2 : AnalyticAt ℂ ((ψ x) ∘ (RW.A.chart l).symm) z := (hC.1 l).1 z hz'
    have h3 : AnalyticAt ℂ (fun w => ((ψ x) ∘ (RW.A.chart l).symm) w (i₀ x)) z :=
      analyticAt_pi_iff.1 h2 (i₀ x)
    exact h1.mul h3
  · have hx : 0 < (potA M τ a k₀).h (RW.lift x w) :=
      (potA M τ a k₀).pos _ (RW.mem x w ((hL x).2.2.2.2.1 hw.1)).1
    have hx' : 0 < (potA M τ a k₀).h (RW.lift x' w) :=
      (potA M τ a k₀).pos _ (RW.mem x' w ((hL x').2.2.2.2.1 hw.2)).1
    have hg := locSec_norm_eq K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x x' (ψ x) (ψ x') (kb x) (kb x') (σ x) (σ x')
      (i₀ x) (i₀ x') (V x) (V x') (u x) (u x') hblk hW (hL x) (hL x') w hw
    have key : ∀ (s h : ℝ), 0 < h → s * Real.exp (-(Real.log h + c)) = s / h * Real.exp (-c) := by
      intro s h hh
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log h), Real.exp_log hh, div_eq_mul_inv, mul_assoc]
    show ‖u x w * ψ x w (i₀ x)‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x w)) + c)) =
      ‖u x' w * ψ x' w (i₀ x')‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x' w)) + c))
    rw [key _ _ hx, key _ _ hx', hg]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticePullSplitInjectionStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pull_split_injection : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (E E₁ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (ι : E →ₗ[Ω] E₁) (π : E₁ →ₗ[Ω] E) (L : Lat ξ E) (r : ℕ) (c : Fin r → E) (u : Matrix (Fin r) (Fin r) G), π ∘ₗ ι = LinearMap.id → ((L.map ι).pull ξ' f (TensorProduct.mk Ω G E₁ 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) → (L.pull ξ' f (TensorProduct.mk Ω G E 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E 1 (c l)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap.isFlagVBOn_pull_of_map | exact GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap.isFlagVBOn_pull_of_map | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap.isFlagVBOn_pull_of_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LemmaETailMass
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit in

theorem lemmaETailMass : GroundTheory.Heights₂.Heights.AnalyticLimit.LemmaETailMass.Statement :=
  LemmaETailMass.proof LemmaETrunc.proof LemmaETruncMass.proof
    (LemmaETruncTail.proof LemmaEScale.proof LemmaEEnergy.proof LemmaEWeight.proof
      LogNormSecIntegrable.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_inclusion_exclusion : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | exact GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGeneration
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem frames_at_point : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  intro X Ω _ ξ E _ _ κ x L m n r V φ cc hV hli hsp hG P c₁ hc
  obtain ⟨U, hPU, b, hbV, hfr⟩ := (show L.IsVBOn Set.univ r V from hV) P (Set.mem_univ _)
  have hbP : L.IsFrameAt b P := hfr P (Set.mem_univ _) hPU
  obtain ⟨B, hBreg, hCreg, hBC⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hG P c₁ hc b hbP
  have hmem : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • cc l = b a := by
    intro a
    have hba : b a ∈ Submodule.span Ω (Set.range cc) := by
      rw [hsp, ← hbV]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 hba
  choose t ht using hmem
  refine ⟨Matrix.of fun l a => t a l, Matrix.of (fun j a => φ j (b a) / x c₁ ^ m), B, ?_, ?_, hBC, ?_, hBreg⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hli_b := hbP.1
    rw [Fintype.linearIndependent_iff] at hli_b
    have hcol : ∀ l, ∑ a, t a l * v a = 0 := fun l => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv l
    have hsum : ∑ a, v a • b a = 0 := by
      calc ∑ a, v a • b a = ∑ a, v a • ∑ l, t a l • cc l := by simp only [ht]
        _ = ∑ l, (∑ a, t a l * v a) • cc l := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]
        _ = 0 := by simp [hcol]
    exact hv0 (funext fun a => hli_b v hsum a)
  · ext j a
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : ∑ l, φ j (cc l) * t a l = φ j (b a) := by
      rw [← ht a, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h1]
    by_cases hx : x c₁ ^ m = 0
    · exfalso
      have h2 := congrFun (congrFun hBC a) a
      simp [Matrix.mul_apply, hx, Matrix.one_apply] at h2
    · field_simp
  · intro j a
    exact hCreg j a

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorOfRegularMatrixValueStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_of_regular_matrix_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (N : ℕ) (A : Matrix (Fin N) (Fin N) Ω), z ∈ mcPts (mCoordIdeal x) → (∀ a b, RegAt x (mCoordIdeal z) (A a b)) → ∀ I J : Finset (Fin N), RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (Matrix.of fun a b => valAt x (A a b) z) I J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.regAt_minorIJ_valAt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.regAt_minorIJ_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.regAt_minorIJ_valAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonemptyStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_points_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, ι k) → Ω), (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → (mcPts (mCoordIdeal x)).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockFieldStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_in_block_field : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField <;> assumption)
end

