import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0571
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairing
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_extend {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K))
    (hs : Submodule.span K (L : Set (Fin m → K)) = ⊤) (φ : L →ₗ[𝓞 K] 𝓞 K) :
    ∃ G : (Fin m → K) →ₗ[K] K, ∀ x : L, G x = algebraMap (𝓞 K) K (φ x) := by
  classical
  have hs' : ⊤ ≤ Submodule.span K (L : Set (Fin m → K)) := hs.ge
  obtain ⟨ι, b, hb⟩ : ∃ (ι : Type) (b : Module.Basis ι K (Fin m → K)), ∀ i, b i ∈ L :=
    ⟨_, Module.Basis.ofSpan hs', fun i => Module.Basis.ofSpan_subset hs' ⟨i, rfl⟩⟩
  haveI := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite ι
  let G : (Fin m → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩))
  have hGb : ∀ i, G (b i) = algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩) := fun i => b.constr_basis _ _ _
  refine ⟨G, fun x => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun i => b.repr (x : Fin m → K) i) (S := K)
  choose e he using hd
  have hx : ((d : 𝓞 K) • (x : Fin m → K)) = ∑ i, e i • b i := by
    conv_lhs => rw [← b.sum_repr (x : Fin m → K)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), he i, smul_assoc]
  have hxL : (d : 𝓞 K) • x = ∑ i, e i • (⟨b i, hb i⟩ : L) := by
    apply Subtype.ext
    simpa using hx
  have h1 : (d : 𝓞 K) * φ x = ∑ i, e i * φ ⟨b i, hb i⟩ := by
    have h := congrArg φ hxL
    rw [map_smul, map_sum, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have h2 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = algebraMap (𝓞 K) K ((d : 𝓞 K) * φ x) := by
    have h3 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = G ((d : 𝓞 K) • (x : Fin m → K)) := by
      rw [← algebraMap_smul K (d : 𝓞 K) (x : Fin m → K), map_smul, smul_eq_mul]
    rw [h3, hx, h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), map_smul, hGb, smul_eq_mul, map_mul]
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero d.2
    simpa using this
  rw [map_mul] at h2
  exact mul_left_cancel₀ hd0 h2

theorem mem_of_dot_integral : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K,
    (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  intro K _ _ m L hL v hv
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (𝓞 K) L := inferInstance
  haveI : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let φ : Fin n → L →ₗ[𝓞 K] 𝓞 K := fun i => (LinearMap.proj i).comp s
  let l : Fin n → L := fun i => f (fun j => if i = j then 1 else 0)
  have hdual : ∀ x : L, x = ∑ i, φ i x • l i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    have h2 := LinearMap.pi_apply_eq_sum_univ f (s x)
    rw [h1] at h2
    exact h2
  choose G hG using fun i => exists_extend L hspan (φ i)
  let a : Fin n → Fin m → K := fun i j => G i (fun k => if j = k then 1 else 0)
  have ha : ∀ i w, a i ⬝ᵥ w = G i w := by
    intro i w
    rw [LinearMap.pi_apply_eq_sum_univ (G i) w]
    simp [dotProduct, a, mul_comm]
  have hid : ∀ w : Fin m → K, w = ∑ i, G i w • (l i : Fin m → K) := by
    let T : (Fin m → K) →ₗ[K] (Fin m → K) := ∑ i, (G i).smulRight (l i : Fin m → K)
    have hT : T = LinearMap.id := by
      refine LinearMap.ext_on hspan ?_
      intro x hx
      have h1 := congrArg (Subtype.val) (hdual ⟨x, hx⟩)
      simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have h2 : ∀ i, G i x • (l i : Fin m → K) = φ i ⟨x, hx⟩ • (l i : Fin m → K) := by
        intro i
        rw [show G i x = algebraMap (𝓞 K) K (φ i ⟨x, hx⟩) from hG i ⟨x, hx⟩, algebraMap_smul]
      simp only [h2]
      simpa using h1.symm
    intro w
    have h := LinearMap.congr_fun hT w
    simpa [T, LinearMap.sum_apply] using h.symm
  have hint : ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = a i ⬝ᵥ v := by
    intro i
    have h := hv (a i) (fun x hx => by
      rw [(ha i x).trans (hG i ⟨x, hx⟩)]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩)
    exact Submodule.mem_one.mp h
  choose o ho using hint
  rw [hid v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h3 : G i v • (l i : Fin m → K) = o i • (l i : Fin m → K) := by
    rw [← ha, ← ho, algebraMap_smul]
  rw [h3]
  exact L.smul_mem _ (l i).2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvariety
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderSub

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)
open GlobalTheory.CompanionTheory.MPDict.Onto GlobalTheory.CompanionTheory.MPDict.Under

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem point_eq_pt {N : ℕ} (t : Fin (N + 1) → ℂ) (ht : t ≠ 0) (hu : Ideal.span (Set.range t) = ⊤) :
    GlobalTheory.TuplePoint.point ℤ t ht = GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) t hu := by
  unfold GlobalTheory.TuplePoint.point GlobalTheory.ProjSpace.pt
  congr 1

theorem le_mCoordIdeal_of_mem_mcPts {P : Ideal (Geo.MRing (Bk n))} (hP : Geo.IsMultiHomogIdeal P)
    {z : (Σ k, Bk n k) → ℂ} (hz : z ∈ mcPts P) : P ≤ Geo.mCoordIdeal z := by
  obtain ⟨S, hS, hPS⟩ := hP
  have h0 := hz.2
  rw [hPS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have e : aeval z f = 0 := by
    have := h0 f (hPS ▸ Ideal.subset_span hf)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    simpa using this
  rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, e, C_0, mul_zero]

theorem ptIdeal_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {w : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder w z) :
    ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) = Geo.mCoordIdeal z := by
  have ht := blockVec_ne_zero hz'
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => z ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hz' k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
  let g : Sp ℂ ⟶ MP ℤ m n := w.1
  have hg : ∀ k, g ≫ prB n k = a k := fun k =>
    (comp_of_isUnder ht hz' H k).trans (point_eq_pt _ _ (hu k))
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  let x : MP ℤ m n := g p
  let θ : ℂ →+* (Sp ℂ).residueField p :=
    ((Sp ℂ).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp ℂ).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (z ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (z ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp ℂ).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : ℂ, ((Sp ℂ).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp ℂ).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (z ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  change ptIdeal x = _
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ z,
    ← mCoordIdeal_blockScale (fun k => θ (z ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_cxPt_of_mem_mcPts : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ z hz
  obtain ⟨w, hw, -⟩ := existsUnique_isUnder m n z hz.1
  have hP : ptIdeal (i (genericPoint X)) ≤ ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) := by
    rw [ptIdeal_of_isUnder hz.1 hw]
    exact le_mCoordIdeal_of_mem_mcPts (isMultiProjPrime_ptIdeal m n _).2.1 hz
  have hs := (GlobalTheory.T.specializes_iff_point_ideal_le m n _ _).2 hP
  have hr : w.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range i :=
    hs.mem_closed i.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨f, hf⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i w.1 Set.univ dense_univ
    fun q _ => by rwa [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]
  refine ⟨⟨f, by rw [← Category.assoc, hf]; exact w.2⟩, ?_⟩
  have e : PtsOver.map i rfl _ (⟨f, by rw [← Category.assoc, hf]; exact w.2⟩ : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) = w :=
    Subtype.ext hf
  rw [e]
  exact hw

end GlobalTheory.CompanionTheory.MPDict.UnderSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinates
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mchart_zero (n : Fin 1 → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : k = 0 := Fin.fin_one_eq_zero k
  exact hx

theorem mchart_succ {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun j => Set.mem_iInter.1 hx j.succ⟩,
    fun hx => Set.mem_iInter.2 fun k => ?_⟩
  induction k using Fin.cases with
  | zero => exact hx.1
  | succ j => exact Set.mem_iInter.1 hx.2 j

theorem multiprojectivePoint_fst {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (ptP (n 0) (c 0) (fun i => z ⟨0, i⟩)).1 :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ 0

theorem multiprojectivePoint_snd {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩)).1 :=
  pullback.lift_snd _ _ _

theorem multiprojective_chart_affine_holomorphic_points (m : ℕ) : ∀ (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  induction m with
  | zero =>
    intro n c
    have key : ∀ W : (MP ℤ 0 n).Opens, W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ 0 n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ 0 n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ 0 n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      have hpt : ∀ z : (Σ k, Bk n k) → ℂ, multiprojectivePoint c z = ptP (n 0) (c 0) (fun i => z ⟨0, i⟩) := fun z => rfl
      refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), fun z _ => ?_, fun a => ?_⟩
      · rw [hpt]
        exact CxPts.ofHom_mem _ _ _
      · have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
          differentiable_pi.2 fun i => differentiable_apply _
        exact (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL.differentiableOn fun z hz => hz 0
    exact key _ (mchart_zero n c)
  | succ m ih =>
    intro n c
    obtain ⟨hA, hM, hD⟩ := ih (Fin.tail n) (fun j => c j.succ)
    have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩) :=
      differentiable_pi.2 fun p => differentiable_apply _
    have hL0 : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
      differentiable_pi.2 fun i => differentiable_apply _
    have hT : Set.MapsTo (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
        {z : (Σ k, Bk (Fin.tail n) k) → ℂ | ∀ k, z ⟨k, c k.succ⟩ ≠ 0} := fun z hz k => hz k.succ
    have main := GlobalTheory.CompanionTheory.Ar.ProdHolo.differentiableOn_ev_prod (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) σ₀
      {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} (chart ℤ (n 0) (c 0))
      (mchart (n := Fin.tail n) (fun j => c j.succ))
      (isAffineOpen_chart ℤ (n 0) (c 0)) hA
      (fun z => ptP (n 0) (c 0) (fun i => z ⟨0, i⟩))
      (fun z => multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩))
      (multiprojectivePoint c) (multiprojectivePoint_fst n c) (multiprojectivePoint_snd n c)
      (fun z _ => CxPts.ofHom_mem _ _ _) (fun z hz => hM _ (hT hz))
      (fun a => (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL0.differentiableOn fun z hz => hz 0)
      (fun b => (hD b).comp hL.differentiableOn hT)
    have key : ∀ W : (MP ℤ (m + 1) n).Opens,
        W = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
          pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
            mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ (m + 1) n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ (m + 1) n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ (m + 1) n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      exact main
    exact key _ (mchart_succ n c)

theorem mchart_affine_holo : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} :=
  fun m n c => ⟨(multiprojective_chart_affine_holomorphic_points m n c).1, (multiprojective_chart_affine_holomorphic_points m n c).2.2⟩

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbit
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_mem_blockChart (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) :
    ∃ i, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) :=
  ⟨ptChart _ k, GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩

theorem exists_ne_zero_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (k : Fin (m + 1)) : ∃ i, z ⟨k, i⟩ ≠ 0 :=
  (exists_mem_blockChart w k).imp fun i hi => (h k i).1.1 hi

theorem sameOrbit_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z z' : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (h' : IsUnder w z') : SameOrbit z z' := by
  choose c hc using exists_mem_blockChart w
  refine ⟨fun k => z ⟨k, c k⟩ / z' ⟨k, c k⟩,
    fun k => div_ne_zero ((h k _).1.1 (hc k)) ((h' k _).1.1 (hc k)), ?_⟩
  funext ⟨k, j⟩
  have e := ((h k (c k)).2 j (hc k)).symm.trans ((h' k (c k)).2 j (hc k))
  have a := (h k _).1.1 (hc k)
  have b := (h' k _).1.1 (hc k)
  rw [div_eq_div_iff a b] at e
  show z ⟨k, j⟩ = z ⟨k, c k⟩ / z' ⟨k, c k⟩ * z' ⟨k, j⟩
  rw [div_mul_eq_mul_div, eq_div_iff b]
  linear_combination e

theorem eq_iff_sameOrbit (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ)
    (h : IsUnder (PtsOver.map i rfl _ y) z) (h' : IsUnder (PtsOver.map i rfl _ y') z') :
    y = y' ↔ SameOrbit z z' := by
  constructor
  · rintro rfl
    exact sameOrbit_of_isUnder h h'
  · intro ho
    have e := (Under.existsUnique_isUnder m n z (exists_ne_zero_of_isUnder h)).unique h
      (isUnder_of_sameOrbit m n _ z' z h' ho)
    exact Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val e))

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCoverStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_finite_open_cover : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r),
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep | exact GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNorm
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig

theorem norm_eq_mul_conj_and_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  intro F E _ _ _ _ _ σ hσ t
  classical
  obtain ⟨_, hE, hdeg, hconj⟩ := hσ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine ⟨?_, ?_⟩
  · set σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (AlgHom.bijective σ) with hσ'
    have hne : σ' ≠ 1 := by
      intro h
      have hx : ∀ x, σ x = x := fun x => by
        have := congrArg (fun g : E ≃ₐ[F] E => g x) h
        simpa [hσ'] using this
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
      have hwc : w.IsComplex := hE.isComplex w
      rw [InfinitePlace.isComplex_iff] at hwc
      apply hwc
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hconj, hx]
    have hcard_le : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
      rw [← hdeg]
      exact (Fintype.card_le_of_injective (fun g : E ≃ₐ[F] E => (g : E →ₐ[F] E))
        (fun a b h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)).trans AlgHom.card_le
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ'} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Finset.card_pair hne.symm]
      exact hcard_le
    haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by
      rw [hdeg, Nat.card_eq_fintype_card]
      apply le_antisymm hcard_le
      rw [← Finset.card_univ, huniv, Finset.card_pair hne.symm])
    rw [RingOfIntegers.coe_norm, Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne.symm]
    simp [hσ']
  · rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
    congr 1
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, RingOfIntegers.coe_norm, Algebra.norm_norm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPointStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_form_nonzero_on_generic_point : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | exact GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | (intros; apply GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentFormStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilFree_of_congruent_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J' T hT → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry <;> assumption)
end

