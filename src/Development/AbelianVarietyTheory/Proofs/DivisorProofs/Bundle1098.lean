import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvTopOrRat
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem coinv_top_or_rat (P Q R S : ℕ) (x : ℂ) :
    coinv P Q R S x = ⊤ ∨ ∃ x' : ℚ, coinv P Q R S x = coinv P Q R S (x' : ℂ) := by
  by_cases hx : ∃ x' : ℚ, x = x'
  · obtain ⟨x', rfl⟩ := hx
    exact Or.inr ⟨x', rfl⟩
  push_neg at hx
  by_cases hI : IsEmpty (Ix P Q)
  · right
    refine ⟨0, ?_⟩
    unfold coinv
    congr 1
    ext g
    simp [Matrix.trace, Finset.univ_eq_empty]
  · left
    rw [not_isEmpty_iff] at hI
    obtain ⟨a⟩ := hI
    let K : Subring ℂ := (Rat.castHom ℂ).range
    have hxK : x ∉ K := by
      rintro ⟨q, hq⟩
      exact hx q hq.symm
    have hsign : ∀ c : Ix R S, lineSign a c ∈ K := by
      intro c
      rcases a with a | a <;> rcases c with c | c <;> simp only [lineSign] <;>
        first | exact K.one_mem | exact K.neg_mem K.one_mem
    have hc : ∀ α : Ln P Q R S →₀ ℕ, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) ∈ K := by
      intro α
      refine K.sum_mem fun c _ => K.mul_mem (hsign c) (K.add_mem (natCast_mem K _) ?_)
      exact RingHom.mem_range.mpr ⟨1 / 2, by simp⟩
    have hmon : ∀ α : Ln P Q R S →₀ ℕ, (MvPolynomial.monomial α (1 : ℂ) : Pol P Q R S) ∈ coinv P Q R S x := by
      intro α
      have hne : (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x ≠ 0 := by
        intro h
        apply hxK
        rw [sub_eq_zero] at h
        rw [← h]
        exact hc α
      have hg : fockAct1 P Q R S (Eab a a) (MvPolynomial.monomial α 1) -
          (x * (Eab a a : Mat P Q).trace) • MvPolynomial.monomial α 1 ∈ coinv P Q R S x :=
        Submodule.subset_span ⟨Eab a a, _, rfl⟩
      have htr : (Eab a a : Mat P Q).trace = 1 := by simp [Eab]
      rw [cartan1, htr, mul_one, ← sub_smul] at hg
      have h2 := (coinv P Q R S x).smul_mem ((∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x)⁻¹ hg
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    rw [eq_top_iff]
    intro f _
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have he : (MvPolynomial.monomial α (MvPolynomial.coeff α f) : Pol P Q R S) =
        MvPolynomial.coeff α f • MvPolynomial.monomial α 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he]
    exact (coinv P Q R S x).smul_mem _ (hmon α)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.TorusNorm

theorem exists_compact_mod_sim (Z S : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [SigmaCompactSpace S]
    [T2Space S] (hZ : ∀ a b : Z, a * b = b * a) (hS : ∀ a b : S, a * b = b * a)
    (τ : Z →* Z) (hτc : Continuous τ) (hτi : ∀ z, τ (τ z) = z)
    (hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s)
    (ι : S →* Z) (hιc : Continuous ι) (hτι : ∀ a, τ (ι a) = ι a)
    (hU : ∃ U ∈ nhds (1 : S), ∀ a ∈ U, a * a = 1 → a = 1) (D : Set Z) (hD : IsCompact D) :
    ∃ B : Set Z, IsCompact B ∧ ∀ (z : Z) (a : S), τ z * z * (ι a)⁻¹ ∈ D →
      ∃ u : Z, ∃ l : S, τ u * u = ι l ∧ ∃ b ∈ B, z = u * b := by
  let T : Z × S →* Z × S :=
    { toFun := fun h => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
      map_one' := by simp
      map_mul' := fun h k => by
        ext
        · show τ (h.1 * k.1) * (ι (h.2 * k.2))⁻¹ = τ h.1 * (ι h.2)⁻¹ * (τ k.1 * (ι k.2)⁻¹)
          rw [map_mul, map_mul, _root_.mul_inv_rev, hZ (ι k.2)⁻¹ (ι h.2)⁻¹]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, hZ (ι h.2)⁻¹ (τ k.1)]
        · show (h.2 * k.2)⁻¹ = h.2⁻¹ * k.2⁻¹
          rw [_root_.mul_inv_rev, hS] }
  have hT : ∀ h, T h = (τ h.1 * (ι h.2)⁻¹, h.2⁻¹) := fun h => rfl
  have hcomm : ∀ a b : Z × S, a * b = b * a := fun a b => Prod.ext (hZ _ _) (hS _ _)
  have hTc : Continuous T := by
    show Continuous fun h : Z × S => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
    exact ((hτc.comp continuous_fst).mul (hιc.comp continuous_snd).inv).prodMk continuous_snd.inv
  have hTi : ∀ h, T (T h) = h := by
    intro h
    rw [hT, hT]
    ext
    · simp only [map_mul, map_inv, hτi, hτι, inv_inv]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp
  obtain ⟨W, hW, hWs⟩ := hsq
  obtain ⟨U, hU1, hUs⟩ := hU
  have hsqT : ∃ W' ∈ nhds (1 : Z × S), ∀ s ∈ W', T s = s → ∃ r : Z × S, T r = r ∧ r * r = s := by
    refine ⟨W ×ˢ U, prod_mem_nhds hW hU1, fun s hs hTs => ?_⟩
    have h2 : s.2⁻¹ = s.2 := congrArg Prod.snd hTs
    have ha : s.2 = 1 := hUs _ hs.2 (by
      calc s.2 * s.2 = s.2 * s.2⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _)
    have h1 : τ s.1 * (ι s.2)⁻¹ = s.1 := congrArg Prod.fst hTs
    rw [ha, map_one, inv_one, mul_one] at h1
    obtain ⟨r, hr, hrr⟩ := hWs _ hs.1 h1
    refine ⟨(r, 1), ?_, ?_⟩
    · rw [hT]; simp [hr]
    · ext
      · exact hrr
      · simp [ha]
  haveI : T2Space (Z × S) := inferInstance
  obtain ⟨B, hB, hBs⟩ := GlobalTheory.InvolutionNorm.exists_compact_mod_kernel (Z × S) hcomm T hTc hTi hsqT
    (D ×ˢ {1}) (hD.prod isCompact_singleton)
  refine ⟨Prod.fst '' B, hB.image continuous_fst, fun z a hz => ?_⟩
  have hmem : T (z, a) * (z, a) ∈ D ×ˢ ({1} : Set S) := by
    rw [hT]
    refine ⟨?_, ?_⟩
    · show τ z * (ι a)⁻¹ * z ∈ D
      rw [mul_assoc, hZ (ι a)⁻¹ z, ← mul_assoc]; exact hz
    · show a⁻¹ * a = 1
      exact inv_mul_cancel a
  obtain ⟨t, ht, b, hb, hzb⟩ := hBs _ hmem
  refine ⟨t.1, t.2, ?_, b.1, ⟨b, hb, rfl⟩, congrArg Prod.fst hzb⟩
  have h1 : τ t.1 * (ι t.2)⁻¹ * t.1 = 1 := congrArg Prod.fst ht
  rw [mul_assoc, hZ _ t.1, ← mul_assoc] at h1
  exact mul_inv_eq_one.1 h1

end GlobalTheory.OrbFinAf.TorusNorm

namespace GlobalTheory.OrbFinAf.TorusNorm

end GlobalTheory.OrbFinAf.TorusNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFiniteAdelesAwayPBoundedDenominatorsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  first | (exact @GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (exact GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (intros; apply GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

open scoped ComplexOrder

open Formalism.IndefR.Cx.GroupActionMatrices Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition Formalism.L2.DIV.CyclotomicLifting in

theorem csum_eigSum_orth {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v : InfinitePlace K} {s : ℕ} {op : I → Module.End K B.S.Forms}
    (h : BlockHyp B ℓ v s) (hO : OkOp B op) {C C' : (I → K) → Prop} (hCC : ∀ x, C' x → ¬ C x) {f g : B.S.Forms}
    (hf : f ∈ Formalism.L2.Col.eigSum op C) (hg : g ∈ Formalism.L2.Col.eigSum op C') :
    B.S.csum (f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = 0 := by
  classical
  have hA : (B.S.H.map v.embedding).PosDef := h.ok.hpos v
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v)
  have hadj : ∀ i, ∃ i', B.S.H.map v.embedding * (oM B op i).map v.embedding =
      ((oM B op i').map v.embedding)ᴴ * B.S.H.map v.embedding := by
    intro i
    obtain ⟨i', hi'⟩ := oM_adj hO i
    have h2 : B.S.H * oM B op i = (oM B op i')ᴴ * B.S.H := by
      have := congrArg Matrix.conjTranspose hi'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
      exact this
    refine ⟨i', ?_⟩
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax v.embedding _ (hO.rat i')]
  have hc : Formalism.L2.Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, oM_comm hO.comm])
  have hs : Formalism.L2.Col.SplitOver (linF fun i => (oM B op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hmem : ∀ {S : (I → K) → Prop} {z : B.S.Forms}, z ∈ Formalism.L2.Col.eigSum op S →
      (fun a => v.embedding (B.S.basis.equivFun z a)) ∈ Formalism.L2.Col.eigSum (linF fun i => (oM B op i).map v.embedding)
        (fun w => ∃ x, S x ∧ w = fun i => v.embedding (x i)) := by
    intro S z hz
    have h1 : B.S.basis.equivFun z ∈ Formalism.L2.Col.eigSum (fun i => Matrix.toLin' (oM B op i)) S := by
      have := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i)) (fun i f => by rw [Matrix.toLin'_apply]; exact equivFun_oM i f) _ hz
      simpa [Submodule.mem_comap] using this
    exact emb_mem_eigSum v.embedding (oM B op) S h1
  have hCC' : ∀ w, (fun w => ∃ x, C' x ∧ w = fun i => v.embedding (x i)) w →
      ¬ (fun w => ∃ x, C x ∧ w = fun i => v.embedding (x i)) w := by
    rintro w ⟨x', hx', rfl⟩ ⟨x, hx, e⟩
    have : x' = x := funext fun i => v.embedding.injective (by simpa using congrFun e i)
    subst this
    exact hCC x' hx' hx
  have key := cx_eig_orth (fun i => (oM B op i).map v.embedding) (B.S.H.map v.embedding) hA hadj hc hs hCC' (hmem hf) (hmem hg)
  have hform0 : hform B.S.H (B.S.basis.equivFun f) (B.S.basis.equivFun g) = 0 := by
    apply v.embedding.injective
    rw [map_zero, ← key, RationalHermitianForm.hform_eq_dot, ← emb_mulVec v.embedding B.S.H]
    simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.conj]
    rfl
  rw [hform_eq_csum, CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at hform0
  exact hform0

end GlobalTheory.Div

namespace GlobalTheory.Div

set_option maxHeartbeats 1000000 in

theorem inner_jX_csum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms) :
    Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
  rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
  congr 1
  exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y

theorem inner_jX_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms)
    (h : (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) = 0) :
    inner ℂ (R.jX t x) (R.jX t y) = 0 := by
  have key := inner_jX_csum R hM t x y
  have h1 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) = 0 :=
    key.trans ((congrArg (⇑A.v0.embedding) h).trans (map_zero A.v0.embedding))
  exact (map_eq_zero (Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0))).1 h1

end GlobalTheory.Div

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Div.parts_orth_complex : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH p q hpq x hx y hy
  have hok := hOk.ok2.what₂ A3.A.μ0
  have hO := okOp_opAll hok (hOk.what₂ A3.A.μ0) (hH A3.A.μ0).1 (hH A3.A.μ0).2
  have hSS : ∀ z, (A3.rowI A3.A.μ0).HasRes3 q.1 z → ¬ (A3.rowI A3.A.μ0).HasRes3 p.1 z := fun z hq =>
    (A3.rowI A3.A.μ0).excl3 ((A3.rowI A3.A.μ0).diffAt_of_mem_ixFin3 q.2 p.2 fun e => hpq (Subtype.ext e).symm) z hq
  have hblk : BlockHyp (A3.A.fam.R A3.A.μ0) (A3.A.fam.lvl F.P0 F.ψ0) A3.A.fam.v0 s := ⟨hOk.ok2.conj, hOk.ok2.irr, hok⟩
  have hgen : ∀ f ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1, ∀ g ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1,
      ⟪R.jX A3.A.μ0 f, R.jX A3.A.μ0 g⟫_ℂ = 0 := by
    intro f hf g hg
    have h0 := GlobalTheory.Div.csum_eigSum_orth hblk hO hSS hf hg
    exact GlobalTheory.Div.inner_jX_zero R.toRealDat hC.base.models A3.A.μ0 f g h0
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, hf, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, hg, rfl⟩ := hb
      exact hgen f hf g hg
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_right, hu, hw, add_zero]
    | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapMemMult
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.ConjFull

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_mem_mult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    {J : Set (GA D V)} {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = star (χ k)) {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    conjMap M M' c h T ∈ Mult θ M' J χ' := by
  obtain ⟨T', hT', e1⟩ := (GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc).2 J χ T hT
  have : conjMap M M' c h T = T' := by
    refine MultilinearMap.ext fun v' => funext fun g => ?_
    rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
    rfl
  rw [this]
  exact mult_congr θ M' hχ hT'

theorem heckeLin_star (R : Finset (GA D V)) (φ : GA D V → ℂ) : heckeLin V R (star φ) = star (heckeLin V R φ) := by
  funext g
  show ∑ γ ∈ R, star (φ (g * γ)) = star (∑ γ ∈ R, φ (g * γ))
  rw [star_sum]

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a a' : Pl D.host.E → List ℤ → ℂ)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (hχ0 : ∀ k ∈ J0, χ0 k = star (χ0 k))
    (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) (ha : ∀ P d, a' P d = star (a P d)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
  have h := (GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc).1
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨conjMap_mem_mult θ M M' c hc h hχ h1, ?_⟩, ?_⟩
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · obtain ⟨h4, h5⟩ := (mem_partFull θ M J0 χ0 SF a T).1 h3
      refine (mem_partFull θ M' J0 χ0 SF a' _).2 ⟨conjMap_mem_mult θ M M' c hc h hχ0 h4, fun P d R hR v' => ?_⟩
      rw [conjMap_apply, heckeLin_star, h5 P d R hR, star_smul, ha]
  let j : (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank_full : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), (∀ k ∈ J, χ' k = star (χ k)) → (∀ k ∈ J0, χ0 k = star (χ0 k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF (fun P d => star (a P d)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J J0 χ χ' χ0 e e' SF a hχ hχ0 he
  refine le_antisymm (rank_le θ M M' c hc J J0 χ χ' χ0 e e' SF a _ hχ hχ0 he fun _ _ => rfl) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J J0 χ' χ χ0 e' e SF _ a ?_ hχ0 ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P d
    simp

end GlobalTheory.ConjFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGroStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_torsionTranslateCombination_entire_gaussianGrowth : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  first | exact @GlobalTheory.ConjComb.conj_pres | exact GlobalTheory.ConjComb.conj_pres | (intros; apply GlobalTheory.ConjComb.conj_pres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponentStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryOneParameter_realPlaceComponent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} (γ : Multiplicative ℝ →* UG (cA σ) J), Continuous γ → ∀ (w : InfinitePlace F) (τ : EmbOver E w), Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  first | exact @GlobalTheory.ContMapReal.contmap | exact GlobalTheory.ContMapReal.contmap | (intros; apply GlobalTheory.ContMapReal.contmap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CoreOfWeak

theorem core_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → Core R.toRealDat F.lv2 ∧ IsSF R.toRealDat R.SF ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ ∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h e
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak h e
  refine ⟨⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩, ?_, fun c => rfl, fun i c => rfl⟩
  intro v
  rw [h.inert.SF v, h.allPl]

end GlobalTheory.CoreOfWeak
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeTheoremPicardGroupStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_theorem_picardGroup : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B), GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) = GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) + GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  first | exact @GlobalTheory.CubeThm.cube_pic | exact GlobalTheory.CubeThm.cube_pic | (intros; apply GlobalTheory.CubeThm.cube_pic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffMulPolyMemCcMat
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.CutoffPoly

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun M : Fin n → Fin n → ℂ => M i j) :=
  (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin n → ℂ) i)

theorem contDiff_eval {X σ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : σ → X → ℂ)
    (hc : ∀ s, ContDiff ℝ ∞ (c s)) (P : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval (fun s => c s x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p s hp => simpa using hp.mul (hc s)

theorem cutoff_mul_poly_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (R : ℝ), ContDiff ℝ ∞ F → (∀ x, R ≤ x → F x = 0) → ∀ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) ∈ CcMat (ujMat ε) := by
  intro n ε F R hF hR P
  refine mem_ccSmooth.2 ⟨?_, fun M : Fin n → Fin n → ℂ =>
    ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) *
      MvPolynomial.eval (fun s => Sum.elim (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => M z.1 z.2)
        (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => star (M z.1 z.2)) s M) P, ?_, ?_⟩
  · refine HasCompactSupport.intro (GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε R) fun g hg => ?_
    have h : R ≤ ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 :=
      (not_le.1 hg).le
    rw [hR _ h]; simp
  · refine ContDiff.mul (Complex.ofRealCLM.contDiff.comp (hF.comp ?_)) (contDiff_eval _ ?_ P)
    · exact ContDiff.sum fun z _ => (contDiff_norm_sq ℂ).comp (contDiff_entry _ _)
    · rintro (z | z)
      · exact contDiff_entry _ _
      · exact Complex.conjCLE.contDiff.comp (contDiff_entry z.1 z.2)
  · intro g
    congr 3
    funext s
    rcases s with z | z <;> rfl

end GlobalTheory.CutoffPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ), (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → (∀ y, IsUnitFr X y → ∃ ℓ : Frame X.Ψ r →L[ℝ] ℂ, HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0 ∧ ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X, Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) → DifferentiableOn ℂ Q X.dom := by
  first | exact @GlobalTheory.HolRead.Holo.differentiableOn_of_killed | exact GlobalTheory.HolRead.Holo.differentiableOn_of_killed | (intros; apply GlobalTheory.HolRead.Holo.differentiableOn_of_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanksStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks : GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes.FormalGroupTypes := by
  first | exact @GlobalTheory.PrimePart.formalGroupTypes | exact GlobalTheory.PrimePart.formalGroupTypes | (intros; apply GlobalTheory.PrimePart.formalGroupTypes <;> assumption)
end

