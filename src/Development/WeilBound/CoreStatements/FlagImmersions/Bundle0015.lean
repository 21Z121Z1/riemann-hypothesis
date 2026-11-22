import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0158

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.CptEx
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

private theorem noetherianSpace_projectiveSpectrum {A σ : Type} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [IsNoetherianRing A] : TopologicalSpace.NoetherianSpace (ProjectiveSpectrum 𝒜) := by
  let f : ProjectiveSpectrum 𝒜 → PrimeSpectrum A := fun p => ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  have hf : Topology.IsInducing f := by
    refine ⟨TopologicalSpace.ext_iff_isClosed.2 fun s => ?_⟩
    rw [isClosed_induced_iff, ProjectiveSpectrum.isClosed_iff_zeroLocus]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨PrimeSpectrum.zeroLocus t, PrimeSpectrum.isClosed_zeroLocus t, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
      refine ⟨u, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  exact hf.noetherianSpace

theorem cptEx : CptEx := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐
  have hfr : ∀ x : ↥c.F, ∃ (a b : 𝓞 ↥c.F), (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 ∧ x * (algebraMap (𝓞 ↥c.F) ↥c.F) b = (algebraMap (𝓞 ↥c.F) ↥c.F) a := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥c.F) x
    have hb' : (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩
  have hinj : Function.Injective (algebraMap (𝓞 ↥c.F) ↥c.F) := IsFractionRing.injective _ _
  obtain ⟨hpre, hflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.spMap_flat_preimmersion (algebraMap (𝓞 ↥c.F) ↥c.F) hinj hfr
  obtain ⟨jpre, jflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.j_flat_preimmersion Y hinj hfr
  haveI := hpre
  haveI := jpre
  haveI := Y.jQ_open
  haveI : TopologicalSpace.NoetherianSpace Y.X := by
    obtain ⟨N, i, hi, -⟩ := Y.proj
    have : TopologicalSpace.NoetherianSpace (PSpace (𝓞 ↥c.F) N) := by
      unfold PSpace
      letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := 𝓞 ↥c.F)
      exact noetherianSpace_projectiveSpectrum _
    exact i.isClosedEmbedding.isInducing.noetherianSpace
  have hfx : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := GlobalTheory.CompanionTheory.Ar.Dominates.map_genPt 𝔐.fn_over
  have hsx : Y.s (genPt 𝔐.ξ₀) ∈ Set.range (spMap (algebraMap (𝓞 ↥c.F) ↥c.F)) := by
    refine ⟨spMap 𝔐.cst (IsLocalRing.closedPoint Ω), ?_⟩
    have h2 := congrArg (fun g => g (IsLocalRing.closedPoint Ω)) 𝔐.cst_over
    have h3 : spMap (𝔐.cst.comp (algebraMap (𝓞 ↥c.F) ↥c.F)) = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 ↥c.F) ↥c.F) := by
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [h3] at h2
    simp only [Scheme.Hom.comp_apply] at h2
    rw [← hfx]
    exact h2.symm
  have hsx2 : genPt 𝔐.ξ₀ ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact hsx
  obtain ⟨x', hx'⟩ := hsx2
  have hgen : ∀ {p z : ↥Y.X}, genPt 𝔐.ξ₀ ⤳ p → z ⤳ p → genPt 𝔐.ξ₀ ⤳ z := fun hp hz =>
    GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes 𝔐.ξ₀ 𝔐.gen₀ hp hz
  have hopen : IsOpen (closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.isOpen_of_isClosed_of_generizing _ isClosed_closure ?_
    intro a b hab hb
    exact specializes_iff_mem_closure.1 (hgen (specializes_iff_mem_closure.2 hb) hab)
  have hV : IsOpen ((pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base ⁻¹' closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) :=
    hopen.preimage (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).continuous
  obtain ⟨q, hqV, u0, rfl⟩ := Y.jQ_dense.inter_open_nonempty _ hV
    ⟨x', by
      show (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base x' ∈ closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)
      rw [hx']
      exact subset_closure rfl⟩
  have hsp : x' ⤳ Y.jQ u0 := by
    rw [← (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).isEmbedding.isInducing.specializes_iff, hx']
    exact specializes_iff_mem_closure.2 hqV
  obtain ⟨u, hu⟩ := hsp.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨u0, rfl⟩
  have hju : Y.j u = genPt 𝔐.ξ₀ := by
    show (Y.jQ ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base u = genPt 𝔐.ξ₀
    rw [Scheme.Hom.comp_apply, hu, hx']
  have hmin : ∀ z, z ⤳ u → z = u := by
    intro z hz
    have h1 : Y.j z ⤳ genPt 𝔐.ξ₀ := hju ▸ hz.map Y.j.continuous
    have h2 : genPt 𝔐.ξ₀ ⤳ Y.j z := hgen (specializes_refl _) h1
    exact Y.j.isEmbedding.injective ((h1.antisymm h2).eq.trans hju.symm)
  obtain ⟨U, hU, huU⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {u} isIrreducible_singleton
  obtain ⟨Z⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nonempty_cptOver_of_fraction hinj hfr Y U hU
  have hZu : genPt Z.ξ₀ = u := hmin _ ((Z.closure u).1 (huU rfl))
  obtain ⟨U', hU', -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain E H D l Xo c (𝓞 ↥c.F) (algebraMap (𝓞 ↥c.F) ↥c.F) Y U Z
    ⟨hinj, inferInstance, hfr⟩
  refine ⟨U, Z, ⟨isClosed_of_mem_irreducibleComponents U hU, hU' ▸ U'.isOpen⟩, hU.1, ?_⟩
  have : genPt (Z.ξ₀ ≫ Y.j) = Y.j (genPt Z.ξ₀) := by
    unfold genPt
    exact Scheme.Hom.comp_apply _ _ _
  rw [this, hZu, hju]

end RootFieldNumerics.RF
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.FrameOfMatrix
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_of_val {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : genPt ξ ⤳ centre z) (hv : ValAt ξ z a r) (hr : IsUnit r) : unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨h', x, rfl, rfl⟩ := hv
  obtain ⟨x, rfl⟩ : IsUnit x := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x hr
  exact ⟨(x.isUnit.map (genMap ξ ⟨centre z, h'⟩)).ne_zero, ⟨x.val, rfl⟩, ⟨x⁻¹.val, map_units_inv _ x⟩⟩

variable {L : Type} [Field L] {z : Spec (CommRingCat.of L) ⟶ X}

theorem val_mul {a b : Ω} {r s : L} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

theorem val_pow {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  exact ⟨h, x ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x :=
    (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ hr)
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

theorem val_zpow {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using val_pow h n
  · simpa using val_inv (val_pow h n) (pow_ne_zero _ hr)

end Val

theorem frame_of_matrix {S : Scheme.{0}} {L : Type} [Field L] {G : Over S} [GrpObj G] [IsCommMonObj G] {x₀ : Sp L ⟶ S}
    {W : Type} [AddCommGroup W] [Module L W] (M : LieModel G x₀ W) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End L W) (σ : O →+* L) (hM : M.IsActOf act.act ρ) {n : ℕ} (x : Fin n → W)
    (hx : IsEigFrame act x₀ σ fun k => M.pt (x k)) (P : Matrix (Fin n) (Fin n) L) (hP : P.det ≠ 0) :
    LinearIndependent L (fun k => ∑ i, P k i • x i) ∧ IsEigFrame act x₀ σ (fun k => M.pt (∑ i, P k i • x i)) ∧
      ∀ k, IsComb (P k) (fun i => M.pt (x i)) (M.pt (∑ i, P k i • x i)) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n x hM).1 hx
  have hU : IsUnit P.det := IsUnit.mk0 _ hP
  have key : ∀ u : Fin n → L, ∑ k, u k • ∑ i, P k i • x i = ∑ i, (Matrix.vecMul u P) i • x i := fun u => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have huniq : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → L, e = ∑ k, cf k • ∑ i, P k i • x i := fun e he => by
    obtain ⟨cf, hcf, hu⟩ := h2 e he
    refine ⟨Matrix.vecMul cf P⁻¹, ?_, fun u h => ?_⟩
    · change e = ∑ k, (Matrix.vecMul cf P⁻¹) k • ∑ i, P k i • x i
      rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
      exact hcf
    · have e1 : Matrix.vecMul u P = cf := hu _ (h.trans (key u))
      rw [← e1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
  refine ⟨Fintype.linearIndependent_iff.2 fun u hu k => ?_, ?_, fun k => ?_⟩
  · obtain ⟨cf, -, h0⟩ := huniq 0 (Submodule.zero_mem _)
    have e1 : u = cf := h0 u hu.symm
    have e2 : (0 : Fin n → L) = cf := h0 0 (by simp)
    rw [e1, ← e2]
    rfl
  · exact (GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n (fun k => ∑ i, P k i • x i) hM).2
      ⟨fun k => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i), huniq⟩
  · exact (GlobalTheory.T.is_comb_tangent_iff_linear_sum S L G x₀ W M n x (P k) _).2 rfl

theorem tied_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {F : Type} [Field F]
    {z : Spec (CommRingCat.of F) ⟶ 𝔐.X} {y₀ : Sp F ⟶ Xo.XF c} {vb : epsAt z ⟶ 𝔐.t.G}
    {v v' : epsAt (under y₀) ⟶ Xo.univ.t.G} (h : Tied 𝔐 z y₀ vb v) (h' : Tied 𝔐 z y₀ vb v') : v = v' := by
  obtain ⟨u, h1, h2⟩ := h
  obtain ⟨u', h1', h2'⟩ := h'
  obtain rfl : u = u' := Over.OverMorphism.ext (h2.symm.trans h2')
  exact h1.unique_left h1'

end RootFieldNumerics.RF.Loc
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.HostRd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IpZeroRight
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace RootFieldNumerics.PC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eig {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem ip_sum (R : RiemLat E g Λ) {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (c : κ → ℂ) (u : ι → Fin g → ℂ)
    (w : κ → Fin g → ℂ) :
    R.ip (∑ k, a k • u k) (∑ l, c l • w l) = ∑ k, ∑ l, star (a k) * c l * R.ip (u k) (w l) := by
  simp only [RiemLat.ip, star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ip_conj (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (starRingEnd ℂ) (R.ip x y) = R.ip y x :=
  conj_hermForm R.herm y x

theorem ip_zero_left (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip 0 y = 0 := by simp [RiemLat.ip]

theorem ip_zero_right (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip y 0 = 0 := by simp [RiemLat.ip]

theorem exists_onb (R : RiemLat E g Λ) (W : Submodule ℂ (Fin g → ℂ)) {m : ℕ} (hm : Module.finrank ℂ W = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ i, e i ∈ W) ∧ (∀ i j, R.ip (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ z ∈ W, ∃ α : Fin m → ℂ, z = ∑ i, α i • e i := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_restriction_orthonormal_coords g m R.Hm R.herm R.pos W hm
  have hinj : Function.Injective (c.comp W.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    by_contra h0
    have h1 := R.pos z fun h => h0 (Subtype.ext h)
    have hz' : c z = 0 := hz
    rw [hc z z.2 z z.2, hz'] at h1
    simp at h1
  have hsur : Function.Surjective (c.comp W.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hm])).1 hinj
  choose e he using fun i => hsur (Pi.single i 1)
  refine ⟨fun i => e i, fun i => (e i).2, fun i j => ?_, fun z hz => ⟨c z, ?_⟩⟩
  · have h1 : c (e i) = Pi.single i 1 := he i
    have h2 : c (e j) = Pi.single j 1 := he j
    rw [RiemLat.ip, hc _ (e i).2 _ (e j).2, h1, h2]
    simp [Pi.single_apply, eq_comm]
  · have h : (⟨z, hz⟩ : W) = ∑ i, c z i • e i := by
      apply hinj
      rw [map_sum]
      simp only [map_smul, he]
      ext k
      simp [Pi.single_apply]
    simpa using congrArg Subtype.val h

section Cx

variable (b : Module.Basis (Fin (2 * g)) ℤ Λ)

def Pc (R : RiemLat E g Λ) : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ fun k => R.P (b k)

theorem Pc_apply (R : RiemLat E g Λ) (ξ : Fin (2 * g) → ℂ) : Pc b R ξ = ∑ k, ξ k • R.P (b k) := rfl

def io (a : Λ) : Fin (2 * g) → ℂ := fun k => (b.repr a k : ℂ)

theorem star_io (a : Λ) : star (io b a) = io b a := by
  ext k
  simp [io]

theorem Pc_io (R : RiemLat E g Λ) (a : Λ) : Pc b R (io b a) = R.P a := by
  conv_rhs => rw [← b.sum_repr a]
  rw [Pc_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, io, Int.cast_smul_eq_zsmul]

def act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Fin (2 * g) → ℂ := ∑ k, ξ k • io b (a • b k)

theorem Pc_act (R : RiemLat E g Λ) (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Pc b R (act b a ξ) = R.B a (Pc b R ξ) := by
  rw [act, map_sum, Pc_apply b R ξ, map_sum]
  simp only [map_smul, Pc_io, R.act]

theorem star_act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : star (act b a ξ) = act b a (star ξ) := by
  simp only [act, star_sum, star_smul, star_io, Pi.star_apply]

theorem exists_real (R : RiemLat E g Λ) (e : Fin g → ℂ) : ∃ ξ, star ξ = ξ ∧ Pc b R ξ = e := by
  have he : e ∈ Submodule.span ℝ (Set.range R.P) := by rw [SheetDecomposition.Riem.span_top]; trivial
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨_, star_io b a, Pc_io b R a⟩
  | zero => exact ⟨0, star_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨ξ, h1, h2⟩ := hx
    obtain ⟨ξ', h1', h2'⟩ := hy
    exact ⟨ξ + ξ', by rw [star_add, h1, h1'], by rw [map_add, h2, h2']⟩
  | smul r x _ hx =>
    obtain ⟨ξ, h1, h2⟩ := hx
    exact ⟨(r : ℂ) • ξ, by rw [star_smul, h1]; simp, by rw [map_smul, h2]; rfl⟩

theorem exists_pair (R : RiemLat E g Λ) (e e' : Fin g → ℂ) : ∃ η, Pc b R η = e ∧ Pc b R (star η) = e' := by
  obtain ⟨ξ, h1, h2⟩ := exists_real b R ((2⁻¹ : ℂ) • (e + e'))
  obtain ⟨ξ', h1', h2'⟩ := exists_real b R ((2⁻¹ * Complex.I : ℂ) • (e' - e))
  refine ⟨ξ + Complex.I • ξ', ?_, ?_⟩
  · rw [map_add, map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (2⁻¹ * (e' k - e k)) * Complex.I_mul_I
  · rw [star_add, star_smul, h1, h1', map_add, map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.star_def, Complex.conj_I]
    linear_combination (-2⁻¹ * (e' k - e k)) * Complex.I_mul_I

theorem ext_pair (R : RiemLat E g Λ) {η η' : Fin (2 * g) → ℂ} (h : Pc b R η = Pc b R η')
    (h' : Pc b R (star η) = Pc b R (star η')) : η = η' := by
  let Θ : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) × (Fin g → ℂ) :=
    (Pc b R).prod (Fintype.linearCombination ℂ fun k => star (R.P (b k)))
  have hΘ : ∀ ξ, Θ ξ = (Pc b R ξ, star (Pc b R (star ξ))) := fun ξ => by
    refine Prod.ext rfl ?_
    show ∑ k, ξ k • star (R.P (b k)) = star (∑ k, star ξ k • R.P (b k))
    simp only [star_sum, star_smul, Pi.star_apply, star_star]
  have hs : Function.Surjective Θ := fun ⟨e, e'⟩ => by
    obtain ⟨η, h1, h2⟩ := exists_pair b R e (star e')
    exact ⟨η, by rw [hΘ, h1, h2, star_star]⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [two_mul])).2 hs ?_
  rw [hΘ, hΘ, h, h']

theorem psi_eq (R : RiemLat E g Λ) (ξ ξ' : Fin (2 * g) → ℂ) :
    R.ip (Pc b R ξ) (Pc b R ξ') - R.ip (Pc b R (star ξ')) (Pc b R (star ξ)) =
      ∑ k, ∑ l, star (ξ k) * ξ' l * (2 * (R.form (b l) (b k) : ℂ) * Complex.I) := by
  simp only [Pc_apply, ip_sum]
  rw [Finset.sum_comm (f := fun k l => star (star ξ' k) * star ξ l * R.ip (R.P (b k)) (R.P (b l))), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := Complex.sub_conj (R.ip (R.P (b k)) (R.P (b l)))
  have h2 : (R.ip (R.P (b k)) (R.P (b l))).im = R.form (b l) (b k) := R.im _ _
  rw [ip_conj, h2] at h
  push_cast at h
  rw [← h, Pi.star_apply, Pi.star_apply, star_star]
  ring

end Cx

theorem mem_of_eig {Ψ : Type} [Fintype Ψ] (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ)
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ τ, eigSp B (σ τ) ≤ W) (h' : ∀ τ, eigSp B ((starRingEnd ℂ).comp (σ τ)) ≤ W) :
    W = ⊤ := by
  refine top_unique fun z _ => ?_
  obtain ⟨y, hy, rfl⟩ := SheetDecomposition.Riem.exists_decomp B z
  refine W.sum_mem fun s _ => ?_
  by_cases e : ∃ τ, σ τ = s.comp (algebraMap (𝓞 E) E)
  · obtain ⟨τ, e⟩ := e
    exact h τ (e ▸ hy s)
  · obtain ⟨τ, e'⟩ := not_not.1 (mt (hσ.2 _).2 e)
    refine h' τ ?_
    have : (starRingEnd ℂ).comp (σ τ) = s.comp (algebraMap (𝓞 E) E) := by
      rw [e']
      ext a
      simp
    exact this ▸ hy s

end RootFieldNumerics.PC
end
end

