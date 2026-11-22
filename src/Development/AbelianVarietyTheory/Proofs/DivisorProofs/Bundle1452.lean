import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedDoubleCosetsLocal
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TwOrbFin

section Generic

variable {H : Type} [Group H]

def Bnd (K₀ : Subgroup H) (D : Set H) : Prop := ∃ S : Finset H, ∀ d ∈ D, ∃ s ∈ S, ∃ k ∈ K₀, d = s * k

def Cmd (K₀ : Subgroup H) : Prop := ∀ s : H, ∃ S : Finset H, ∀ k ∈ K₀, ∃ s' ∈ S, ∃ k' ∈ K₀, k * s = s' * k'

variable {K₀ : Subgroup H}

theorem Bnd.mono {D E : Set H} (h : D ⊆ E) (hE : Bnd K₀ E) : Bnd K₀ D := by
  obtain ⟨S, hS⟩ := hE
  exact ⟨S, fun d hd => hS d (h hd)⟩

theorem bnd_finset (S : Finset H) : Bnd K₀ {g | ∃ s ∈ S, ∃ k ∈ K₀, g = s * k} :=
  ⟨S, fun _ hd => hd⟩

theorem bnd_singleton (g : H) : Bnd K₀ {g} :=
  ⟨{g}, fun d hd => ⟨g, Finset.mem_singleton_self _, 1, K₀.one_mem, by rw [hd, mul_one]⟩⟩

theorem Bnd.mul (hc : Cmd K₀) {D E : Set H} (hD : Bnd K₀ D) (hE : Bnd K₀ E) :
    Bnd K₀ {g | ∃ d ∈ D, ∃ e ∈ E, g = d * e} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  obtain ⟨T, hT⟩ := hE
  refine ⟨S.biUnion fun s => T.biUnion fun t => (Sc t).image (s * ·), ?_⟩
  rintro g ⟨d, hd, e, he, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨t, ht, l, hl, rfl⟩ := hT e he
  obtain ⟨s', hs', k', hk', e'⟩ := hSc t k hk
  refine ⟨s * s', Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨s', hs', rfl⟩⟩⟩,
    k' * l, K₀.mul_mem hk' hl, ?_⟩
  calc s * k * (t * l) = s * (k * t) * l := by group
    _ = _ := by rw [e']; group

theorem Bnd.inv (hc : Cmd K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ {g | g⁻¹ ∈ D} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.biUnion fun s => Sc s⁻¹, ?_⟩
  intro g hg
  obtain ⟨s, hs, k, hk, e⟩ := hS _ hg
  obtain ⟨s', hs', k', hk', e'⟩ := hSc s⁻¹ k⁻¹ (K₀.inv_mem hk)
  refine ⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k', hk', ?_⟩
  rw [← e', ← _root_.mul_inv_rev, ← e, inv_inv]

theorem Bnd.map (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ (θ '' D) := by
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.image θ, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  exact ⟨θ s, Finset.mem_image.2 ⟨s, hs, rfl⟩, θ k, hθ k hk, map_mul θ s k⟩

theorem Bnd.iterate (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) (j : ℕ) {D : Set H} (hD : Bnd K₀ D) :
    Bnd K₀ ((⇑θ)^[j] '' D) := by
  induction j with
  | zero => simpa using hD
  | succ j ih =>
    rw [Function.iterate_succ', Set.image_comp]
    exact ih.map θ hθ

theorem nrmG_succ (θ : H →* H) (j : ℕ) (y : H) : nrmG θ (j + 1) y = nrmG θ j y * (⇑θ)^[j] y := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem Bnd.nrm (hc : Cmd K₀) (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) (j : ℕ) {D : Set H} (hD : Bnd K₀ D) :
    Bnd K₀ (nrmG θ j '' D) := by
  induction j with
  | zero =>
    refine (bnd_singleton 1).mono ?_
    rintro _ ⟨d, -, rfl⟩
    simp [nrmG]
  | succ j ih =>
    refine (ih.mul hc (hD.iterate θ hθ j)).mono ?_
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨d, hd, rfl⟩, nrmG_succ θ j d⟩

theorem nrmG_twConj (θ : H →* H) (j : ℕ) (x δ : H) :
    nrmG θ j (x⁻¹ * δ * θ x) = x⁻¹ * nrmG θ j δ * (⇑θ)^[j] x := by
  induction j with
  | zero => simp [nrmG]
  | succ j ih =>
    rw [nrmG_succ, nrmG_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv,
      ← Function.iterate_succ_apply θ j x]
    group

theorem finite_of_bnd (T K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) (D : Set H) (hD : Bnd K₀ D) (P : H → Prop)
    (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set H) (K : Set H) | P (Quotient.out q)}.Finite := by
  obtain ⟨S, hS⟩ := hD
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  let R : Set H := Set.range fun c : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out c : K₀) : H)
  have hR : R.Finite := Set.finite_range _
  have hcov : ∀ k ∈ K₀, ∃ c ∈ R, ∃ l ∈ K, k = c * l := by
    intro k hk
    let c : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
    have h1 : ((Quotient.out c : K₀))⁻¹ * ⟨k, hk⟩ ∈ K.subgroupOf K₀ :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' c))
    refine ⟨((Quotient.out c : K₀) : H), ⟨c, rfl⟩, ((Quotient.out c : K₀) : H)⁻¹ * k, h1, by group⟩
  refine ((S.finite_toSet.prod hR).image fun sc : H × H => DoubleCoset.mk T K (sc.1 * sc.2)).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨c, hc, l, hl, rfl⟩ := hcov k hk
  refine ⟨(s, c), ⟨hs, hc⟩, ?_⟩
  rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
  exact ⟨t, ht, l, hl, by rw [hx]; group⟩

end Generic

theorem bnd_dbl {H : Type} [Group H] {K₀ : Subgroup H} (hc : Cmd K₀) (S : Finset H) :
    Bnd K₀ {g | ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂} := by
  choose Sc hSc using hc
  refine ⟨S.biUnion Sc, ?_⟩
  rintro g ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩
  obtain ⟨s', hs', k', hk', e⟩ := hSc s k₁ hk₁
  exact ⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k' * k₂, K₀.mul_mem hk' hk₂, by rw [e, mul_assoc]⟩

section Specific

variable {p : ℕ} [Fact p.Prime]

theorem sigG_iterate_apply (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    (⇑(sigG G r))^[k] g = ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1,
      fun i => (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i)) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

theorem sigG_iterate_self (G : HTGroup p) {r : ℕ} (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  rw [sigG_iterate_apply]
  refine Prod.ext ?_ (funext fun i => ?_)
  · exact GlobalTheory.LKLoc.sig_iterate_r p (Q0 p) inferInstance 1 r hr g.1
  · exact sigRes_iterate_eq_self p (G.Fw i) G.n r hr (g.2 i)

end Specific

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → regular₂ G γ → IsNrm G r γ δ z → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → {q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent (sigG G r) δ : Set (Gr G r)) (K : Set (Gr G r)) | φ ((Quotient.out q)⁻¹ * δ * sigG G r (Quotient.out q)) ≠ 0}.Finite := by
  intro p _ G r γ δ z K φ hr hγ hN hT
  obtain ⟨hcomm, -, -, S, hS⟩ := hT
  have hc : Cmd (KHT p G.m G.n r G.Fw) := fun s => GlobalTheory.T.finite_left_coset_representatives p G r hr s
  have hσ0 : ∀ k ∈ KHT p G.m G.n r G.Fw, sigG G r k ∈ KHT p G.m G.n r G.Fw :=
    fun k hk => GlobalTheory.LKRes.Model.sigHT_KHT p G.m G.n r G.Fw k hk
  let C : Set (Gr G r) := {g | φ g ≠ 0}
  have hC : Bnd (KHT p G.m G.n r G.Fw) C := (bnd_dbl hc S).mono fun g hg => by
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hS g hg
    exact ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩
  obtain ⟨E, hE⟩ := hC.nrm hc (sigG G r) hσ0 r
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.T.centralizer_finite_decomposition p G r hr γ hγ E
  let A : Set (Gr G r) := {g | ∃ d ∈ D₁, ∃ k ∈ KHT p G.m G.n r G.Fw, g = z⁻¹ * d * k}
  have hA : Bnd (KHT p G.m G.n r G.Fw) A := by
    refine ⟨D₁.image (z⁻¹ * ·), ?_⟩
    rintro g ⟨d, hd, k, hk, rfl⟩
    exact ⟨z⁻¹ * d, Finset.mem_image.2 ⟨d, hd, rfl⟩, k, hk, rfl⟩
  obtain ⟨E₂, hE₂⟩ := (hA.mul hc hC).mul hc ((hA.map (sigG G r) hσ0).inv hc)
  obtain ⟨D₃, hD₃⟩ := GlobalTheory.T.twisted_centralizer_decomposition p G r hr γ hγ δ z hN E₂
  refine finite_of_bnd (K₀ := KHT p G.m G.n r G.Fw) (GlobalTheory.BCT.twCent (sigG G r) δ) K hcomm.1 _
    ((bnd_finset D₃).mul hc hA) (fun x => φ (x⁻¹ * δ * sigG G r x) ≠ 0) ?_
  intro x hx
  have hy : nrmG (sigG G r) r (x⁻¹ * δ * sigG G r x) ∈ nrmG (sigG G r) r '' C := ⟨_, hx, rfl⟩
  obtain ⟨e, he, k, hk, hek⟩ := hE _ hy
  have key : (z * x)⁻¹ * inclG G r γ * (z * x) = e * k := by
    rw [← hek, nrmG_twConj, sigG_iterate_self G hr, hN]; group
  obtain ⟨t, htc, d, hd, k₁, hk₁, hzx⟩ := hD₁ (z * x) ⟨e, he, k, hk, key⟩
  have ht'c : z⁻¹ * t * z * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * (z⁻¹ * t * z) := by
    rw [hN]
    calc z⁻¹ * t * z * (z⁻¹ * inclG G r γ * z) = z⁻¹ * (t * inclG G r γ) * z := by group
      _ = z⁻¹ * (inclG G r γ * t) * z := by rw [htc]
      _ = _ := by group
  have hxe : x = z⁻¹ * t * z * (z⁻¹ * d * k₁) := by
    calc x = z⁻¹ * (z * x) := by group
      _ = _ := by rw [hzx]; group
  have ht' : z⁻¹ * t * z = x * (z⁻¹ * d * k₁)⁻¹ := by rw [hxe]; group
  have hmem : (z⁻¹ * t * z)⁻¹ * δ * sigG G r (z⁻¹ * t * z) ∈
      {g | ∃ u ∈ {g | ∃ a ∈ A, ∃ c ∈ C, g = a * c}, ∃ v ∈ {g | g⁻¹ ∈ sigG G r '' A}, g = u * v} := by
    refine ⟨(z⁻¹ * d * k₁) * (x⁻¹ * δ * sigG G r x), ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, _, hx, rfl⟩,
      (sigG G r (z⁻¹ * d * k₁))⁻¹, ?_, ?_⟩
    · show ((sigG G r (z⁻¹ * d * k₁))⁻¹)⁻¹ ∈ sigG G r '' A
      rw [inv_inv]
      exact ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩
    · rw [ht', map_mul, map_inv]; group
  obtain ⟨e₂, he₂, k₂, hk₂, h₂⟩ := hE₂ _ hmem
  obtain ⟨u, hu, d₃, hd₃, k₃, hk₃, hu'⟩ := hD₃ _ ht'c ⟨e₂, he₂, k₂, hk₂, h₂⟩
  refine ⟨u, hu, d₃ * k₃ * (z⁻¹ * d * k₁), ⟨d₃ * k₃, ⟨d₃, hd₃, k₃, hk₃, rfl⟩, _, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩, ?_⟩
  rw [hxe, hu']; group

end GlobalTheory.TwOrbFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PlaneFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

theorem det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have h2 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [Matrix.mul_apply]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at h3
  intro h0
  rw [h0, Matrix.det_neg] at h3
  simp at h3
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) h3.symm

theorem form_skew {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  have hs : ∀ i j, σ (J i j) = -J j i := fun i j => hJ j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, conj_conj hσ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PlaneFrame

namespace GlobalTheory.PlaneFrame

theorem frame_dual_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧
      Matrix.vecMulVec H'.x (W.J *ᵥ fun i => σ (H'.y i)) + H'.ι * π - Matrix.vecMulVec H'.y (W.J *ᵥ fun i => σ (H'.x i)) = 1 ∧
      IsUnit W₁.J.det := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hinv := conj_conj hσ
  obtain ⟨hrank, hxx, hyy, hxy, horth, hgram, -, hsplit, -, -, -⟩ := hH
  subst hrank
  have hsk := form_skew hσ hW.skew
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [hsk, hxy, map_one]
  have hxι : ∀ u, form σ W.J H'.x (H'.ι *ᵥ u) = 0 := fun u => by rw [hsk, (horth u).1, map_zero, neg_zero]
  have hyι : ∀ u, form σ W.J H'.y (H'.ι *ᵥ u) = 0 := fun u => by rw [hsk, (horth u).2, map_zero, neg_zero]
  have hlin : ∀ (u : Fin d₁ → E) (a b : E) (w : Fin (d₁ + 2) → E),
      form σ W.J (H'.ι *ᵥ u + (a • H'.x + b • H'.y)) w =
        form σ W.J (H'.ι *ᵥ u) w + a * form σ W.J H'.x w + b * form σ W.J H'.y w := by
    intro u a b w
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
  let Φ : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin (d₁ + 2) → E) :=
    H'.ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ H'.x).coprod (LinearMap.toSpanSingleton E _ H'.y))
  have hΦ : ∀ p, Φ p = H'.ι *ᵥ p.1 + (p.2.1 • H'.x + p.2.2 • H'.y) := fun p => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hsplit z hz
    exact ⟨(u, a, b), by rw [hΦ]; abel⟩
  have hinj : Function.Injective Φ := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hsurj
    · simp [Module.finrank_prod]
  let eΦ := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let πl : (Fin (d₁ + 2) → E) →ₗ[E] (Fin d₁ → E) := LinearMap.fst E _ _ ∘ₗ eΦ.symm.toLinearMap
  have hπ : ∀ p, πl (Φ p) = p.1 := by
    intro p
    simp only [πl, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply]
    rw [show Φ p = eΦ p from rfl, LinearEquiv.symm_apply_apply]
  refine ⟨LinearMap.toMatrix' πl, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply]
    have := hπ (u, 0, 0)
    rw [hΦ] at this
    simpa using this
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
    rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
      ← Matrix.mulVec_mulVec, show LinearMap.toMatrix' πl *ᵥ Φ (u, a, b) = πl (Φ (u, a, b)) from
        (Matrix.toLin'_apply _ _).symm.trans (by rw [Matrix.toLin'_toMatrix']), hπ]
    have e1 : (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ Φ (u, a, b) = a := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).2, hxy, hyy]; ring
    have e2 : (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ Φ (u, a, b) = -b := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).1, hxx, hyx]; ring
    rw [e1, e2, hΦ]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
    ring
  · rw [← hgram, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]

    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hJdet : W.J.det ≠ 0 := by
      intro h0
      apply det_ne_zero_of_hasSig _ (hW.sig w)
      rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
    have hJinj : Function.Injective W.J.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJdet))
    have hσinj : Function.Injective σ := fun a b h => by rw [← hinv a, ← hinv b, h]
    have hιinj : Function.Injective H'.ι.mulVec := by
      intro u v h
      have := hinj (a₁ := (u, 0, 0)) (a₂ := (v, 0, 0)) (by rw [hΦ, hΦ]; simpa using h)
      simpa using congrArg Prod.fst this
    intro v v' hvv
    rw [← sub_eq_zero]
    have h0 : (H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, hvv, sub_self]
    set c : Fin d₁ → E := fun j => σ ((v - v') j) with hcdef
    have hc : H'.ι.map σ *ᵥ (v - v') = fun i => σ ((H'.ι *ᵥ c) i) := by
      ext i; simp [Matrix.mulVec, dotProduct, map_sum, c, hinv]
    have h1 : ∀ u, form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = 0 := by
      intro u
      have : form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = u ⬝ᵥ ((H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v')) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.dotProduct_mulVec,
          Matrix.vecMul_transpose, form]
      rw [this, h0, dotProduct_zero]
    have h2 : ∀ z, form σ W.J z (H'.ι *ᵥ c) = 0 := by
      intro z
      obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
      rw [hΦ, hlin, h1, hxι, hyι]; ring
    have h3 : W.J *ᵥ (fun i => σ ((H'.ι *ᵥ c) i)) = 0 := by
      ext i
      have := h2 (Pi.single i 1)
      rw [form, single_dotProduct, one_mul] at this
      simpa using this
    have h4 : H'.ι *ᵥ c = 0 := by
      have := hJinj (h3.trans (Matrix.mulVec_zero _).symm)
      ext i
      exact hσinj ((congrFun this i).trans (map_zero σ).symm)
    have h5 : c = 0 := hιinj (h4.trans (Matrix.mulVec_zero _).symm)
    ext j
    have := congrFun h5 j
    simp only [c, Pi.zero_apply] at this
    simpa using hσinj (this.trans (map_zero σ).symm)

end GlobalTheory.PlaneFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernel
section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

theorem mem_augRk_of_fibre_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hnd hν Ψ hΨ hT
  have hT' : ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n →
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = 0 := fun Y hY => by
    obtain ⟨h, rfl⟩ := GlobalTheory.T.full_rank_normal_form_orbit k n d hnd Y hY
    exact hT h
  obtain ⟨s, hs⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d _ (GlobalTheory.T.isClopen_unit_minor_set k n d).isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ hΨ
  obtain ⟨Φ, hΦ, hS, hdiff, hF⟩ := GlobalTheory.T.clopen_integrability_full_rank_orbit k n d ν _ (GlobalTheory.T.isClopen_unit_minor_set k n d)
    (fun Φ hΦ Y => GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ hΦ Y) s Ψ hΨ hs
  have hA := GlobalTheory.T.smooth_character_orbital_integral_stable k n d ν hν _ (GlobalTheory.T.integral_group_of_unit_minor_stable k n d) (fun E hE Y hY => GlobalTheory.T.unit_minor_stable_integral_group k n d E Y hE hY) Φ hΦ hS
    (fun Y hY => by rw [hF]; exact hT' Y (GlobalTheory.T.rank_eq_of_unit_minor k n d Y hY))
  have e : Ψ = (Ψ - Φ) + Φ := by abel
  rw [e]; exact add_mem hdiff hA

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuelStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel : Quoted → RankLow := by
  first | exact @GlobalTheory.HSCore.RankBound.rankLow | exact GlobalTheory.HSCore.RankBound.rankLow | (intros; apply GlobalTheory.HSCore.RankBound.rankLow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodStableOfIrr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.GoodStableDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare GlobalTheory.BI

theorem isChar_dual {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]

open Formalism.L2.DIV in

theorem coeff_idemOf_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hrec : R.grp_record) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (g : G) :
    (idemOf A.X).coeff g⁻¹ = (idemOf A.X).coeff g := by
  obtain ⟨eR, plg, iso, h1, -, -⟩ := hrec
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  apply D.what₂.embLL.injective
  rw [h1, h1, ← hφ, ← hφ, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ (φ g) (φ g⁻¹)
    (fun v _ => by rw [map_inv, Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)

open Formalism.L2.DIV in

theorem goodStable_of_irr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hirr : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hG : R.IsGrp F) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hI : IdemTie D om) : GoodStable A.X := by
  classical
  have hsym := coeff_idemOf_inv R hG.record hI
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hirr A.X
    (fun ψ g => D.what₂.embLL (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hirr ψ hψ)
      exact isChar_dual ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]
      simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
        map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply D.what₂.embLL.injective
  simpa using hψe g⁻¹

end GlobalTheory.GoodStableDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInvStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  first | exact @GlobalTheory.height_diagonal_le_sum | exact GlobalTheory.height_diagonal_le_sum | (intros; apply GlobalTheory.height_diagonal_le_sum <;> assumption)
end

