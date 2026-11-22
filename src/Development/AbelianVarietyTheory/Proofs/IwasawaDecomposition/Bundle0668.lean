import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DiscreteTopologySpanOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosDefBalancedRealFormCmField
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DefForm

variable {E : Type} [Field E] [NumberField E]

def coordForm (m : ℕ) : (Fin m → 𝓞 E) →ₗ[ℤ] (Fin m → 𝓞 E) →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun y z => ∑ k, ∑ τ : E →+* ℂ, (τ (y k : E) * conj (τ (z k : E))).re)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intro n y z; simp only [Finset.smul_sum, Pi.smul_apply]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; rw [zsmul_eq_mul, zsmul_eq_mul]; simp [mul_left_comm])

theorem sum_sum_mul_re {ι : Type} [Fintype ι] (c : ι → ℝ) (u : ι → ℂ) :
    ∑ a, ∑ b, c a * c b * (u a * conj (u b)).re = Complex.normSq (∑ a, (c a : ℂ) * u a) := by
  rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (c a : ℂ) * u a * ((c b : ℂ) * conj (u b)) = ((c a * c b : ℝ) : ℂ) * (u a * conj (u b)) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem coordForm_mem [IsCMField E] (H : Host E) (m : ℕ) : coordForm (E := E) m ∈ realForms H.bar (Fin m → 𝓞 E) := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · simp only [coordForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  · simp only [coordForm, LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    push_cast
    simp only [H.bar_eq, IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
    ring_nf

theorem coordForm_posDef (m : ℕ) : IsPosDef (coordForm (E := E) m) := by
  classical
  rw [isPosDef_iff_basis (Pi.basis fun _ : Fin m => RingOfIntegers.basis E)]
  intro c hc
  have hw : ∀ k (τ : E →+* ℂ), ∑ a, (c a : ℂ) * τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) =
      ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) := by
    intro k τ
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · exact Finset.sum_congr rfl fun j _ => by simp [Pi.basis_apply]
    · intro k' _ hk'
      exact Finset.sum_eq_zero fun j _ => by simp [Pi.basis_apply, Pi.single_apply, Ne.symm hk']
    · simp
  have hsum : ∑ a, ∑ a', c a * c a' * coordForm m ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a)
      ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a') =
      ∑ k, ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) := by
    simp_rw [← hw, ← sum_sum_mul_re]
    simp only [coordForm, LinearMap.mk₂_apply, Finset.mul_sum]
    calc _ = ∑ a, ∑ k, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ τ : E →+* ℂ, ∑ a', c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hsum]
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hc ?_
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
  ext ⟨k, j⟩
  have h2 : ∀ τ : E →+* ℂ, ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) = 0 := fun τ =>
    Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1
      (h1 k (Finset.mem_univ _)) τ (Finset.mem_univ _))
  have h3 : ∑ j, (c ⟨k, j⟩ : ℂ) • canonicalEmbedding.latticeBasis E j = 0 := by
    ext τ
    simpa [canonicalEmbedding.latticeBasis_apply, integralBasis_apply, canonicalEmbedding.apply_at] using h2 τ
  have := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent _ h3 j
  simpa using this

theorem exists_posDef_realForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) X
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := f) fun x => LinearMap.congr_fun hs x
  refine ⟨pullR s (coordForm m), ⟨fun y z => (coordForm_mem H m).1 _ _, fun a y z => ?_⟩, ?_⟩
  · simp only [pullR_apply, map_smul]
    exact (coordForm_mem H m).2 a _ _
  · intro n x hx c hc
    exact coordForm_posDef m n (s ∘ x) (hx.map' s.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)) c hc

end GlobalTheory.DefForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isLatBasis_of_isLatFam : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  intro n g B K b₀ hK hb₀
  obtain ⟨H, hH⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH]; exact H.zero_mem
  obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hcont : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hev : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ K b₀ → w = 0 := by
    filter_upwards [hcont.eventually hζ] with w hw hwK
    rw [← hζ0]; exact hw.1 hwK
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule H
  have hL : ∀ w, w ∈ L ↔ w ∈ K b₀ := fun w => by
    rw [← hH]; rfl
  haveI : DiscreteTopology L := by
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.1 hev
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Subtype.val ⁻¹' U := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact h0U
      · intro hx; exact Subtype.ext (hU hx ((hL x).1 x.2))
    rw [this]; exact hUo.preimage continuous_subtype_val
  let bs := Module.finBasis ℤ L
  refine ⟨Module.finrank ℤ L, fun i => (bs i : Fin g → ℂ), GlobalTheory.linearIndependent_real_coe_basis bs, fun w => ?_⟩
  have hsp := GlobalTheory.span_range_coe_basis bs
  have hw : w ∈ L ↔ w ∈ Submodule.span ℤ (Set.range fun i => (bs i : Fin g → ℂ)) := by rw [hsp]
  rw [← hL, hw, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem isOpenImmersion_j_id (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  exact h

theorem exists_sab (Y : Model Xo c (RingHom.id c.F)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Y.X) (_ : IsCN R) (hr : Set.range ξ ⊆ Set.range Y.j) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), PolAt t (jK R) ∧ ThetaNZ t.G t.PP.L ∧ ∀ x, x ∈ abLocus t.G := by
  have hj := isOpenImmersion_j_id Y
  have hab : Set.range ξ ⊆ abLocus Y.t.G := hr.trans (range_j_subset_abLocus Y)
  obtain ⟨ξ', hξ'⟩ : ∃ ξ' : Sp R ⟶ Xo.XF c, ξ' ≫ Y.j = ξ := ⟨IsOpenImmersion.lift Y.j ξ hr, IsOpenImmersion.lift_fac _ _ _⟩
  subst hξ'
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp R), Nonempty (SABMap t Y.t (ξ' ≫ Y.j)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (ξ' ≫ Y.j) Y.t
    exact ⟨_, ⟨m⟩⟩
  have m' : SABMap t Y.oF.t ξ' := (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m m).choose
  have hPI : PushInvertible Y.oF.t.G Y.oF.t.PP.L :=
    PushInv.pushInvertible_any GlobalTheory.allSixLaws.2.1.secBaseChangeAny GlobalTheory.allSixLaws.1.globalSectionsRank _ (GlobalTheory.Obj.toPolAV Y.oF)
  refine ⟨t, m, GoodTrait.polAt_of_point Y m (jK R) (jK R ≫ ξ') (Category.assoc _ _ _),
    ThetaLocal.thetaNZ_of_pushInvertible E H _ Y.oF.t hPI R ξ' t m', fun x => ?_⟩
  exact (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).1 (hab ⟨x, rfl⟩)

end GlobalTheory.GenFan.Tri
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSiegelReducedBasisOfPosDefForm
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped MatrixOrder

namespace GlobalTheory.RedTh.RedBasis

theorem sum_sum_eq_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * G i j = c ⬝ᵥ (G *ᵥ c) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_transpose_mul_self {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hs : Gᵀ = G)
    (hp : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * G i j) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ, g.det ≠ 0 ∧ gᵀ * g = G := by
  have hT : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · show Gᴴ = G
      rw [conjTranspose_eq_transpose_of_trivial, hs]
    · by_cases hx : x = 0
      · simp [hx]
      · have := (hp x hx).le
        rw [sum_sum_eq_dotProduct] at this
        simpa using this
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hT
  have hsq : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsq.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hgG : (CFC.sqrt G)ᵀ * CFC.sqrt G = G := by
    rw [hsym, CFC.sqrt_mul_sqrt_self G h0]
  refine ⟨CFC.sqrt G, fun hd => ?_, hgG⟩
  obtain ⟨v, hv, hgv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h := hp v hv
  rw [sum_sum_eq_dotProduct, ← hgG, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hgv] at h
  simp at h

theorem exists_siegel_basis : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y)
    (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y)
    (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧
    ∀ i j, B (b i) (b j) = gram d u i j := by
  intro n Y _ b₀ B hs hB
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => B (b₀ i) (b₀ j)
  obtain ⟨g, hg, hgG⟩ := exists_transpose_mul_self G (by ext i j; simp [G, hs])
    (by simpa [G] using (isPosDef_iff_basis b₀ B).1 hB)
  obtain ⟨γ, k, a, m, hγ, hk, ha, h1, h0, hup, hstep, hdec⟩ :=
    GlobalTheory.ClassFin.HermiteReduction.exists_reduced n g hg
  have hu : IsUnit γ.det := by rcases hγ with h | h <;> rw [h] <;> simp
  let e : Y ≃ₗ[ℤ] Y := Matrix.toLinearEquiv b₀ γ hu
  have hbe : ∀ j, b₀.map e j = ∑ i, γ i j • b₀ i := fun j => by
    simp [e, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hM : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = gram (fun i => a i ^ 2) m := by
    have e1 : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) =
        (g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ)) := by
      rw [← hgG, transpose_mul]; simp only [Matrix.mul_assoc]
    have e2 : (k * diagonal a * m)ᵀ * (k * diagonal a * m) = mᵀ * (diagonal a * (kᵀ * k) * diagonal a) * m := by
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hdec, e2, hk, Matrix.mul_one, diagonal_mul_diagonal, gram]
    simp only [sq]
  refine ⟨b₀.map e, fun i => a i ^ 2, m, ⟨fun i => sq_nonneg _, fun p q hq => ?_, h1, h0, hup⟩,
    fun i => pow_pos (ha i) 2, fun i j => ?_⟩
  · have h2 := hstep p q hq
    have h3 := ha p
    have h4 := ha q
    show a p ^ 2 ≤ 4 * a q ^ 2
    nlinarith
  · rw [← hM, hbe, hbe]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Matrix.mul_apply,
      transpose_apply, map_apply, G, of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.RedTh.RedBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSiegelReductionOrthogonal
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.RedTh

def siegelGlueMat {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (s + m)) (Fin (s + m)) ℝ := fun i j =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun y => a x y) (fun _ => 0) j)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) (fun y => b x y) j) i

@[simp] lemma siegelGlueMat_ll {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin s) : siegelGlueMat a b (Fin.castAdd m x) (Fin.castAdd m y) = a x y := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_lr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin s) (y : Fin m) : siegelGlueMat a b (Fin.castAdd m x) (Fin.natAdd s y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rl {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m) (y : Fin s) : siegelGlueMat a b (Fin.natAdd s x) (Fin.castAdd m y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m) : siegelGlueMat a b (Fin.natAdd s x) (Fin.natAdd s y) = b x y := by
  simp [siegelGlueMat]

lemma gram_apply_glue {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    gram d u i j = ∑ k, u k i * d k * u k j := by
  simp only [gram]
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

lemma siegelGlue_scale {s m : ℕ} (d₁ : Fin s → ℝ) (d₂ : Fin m → ℝ) (h₁ : ∀ i, 0 < d₁ i)
    (h₂ : ∀ i, 0 < d₂ i) :
    ∃ t : ℝ, 0 < t ∧ ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → t * d₁ i ≤ 4 * d₂ j := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨1, one_pos, fun _ j => j.elim0⟩
  · set j0 : Fin m := ⟨0, hm⟩
    have hS : 0 ≤ ∑ i, d₁ i := Finset.sum_nonneg (fun i _ => (h₁ i).le)
    refine ⟨d₂ j0 / (1 + ∑ i, d₁ i), div_pos (h₂ j0) (by linarith), fun i j hj => ?_⟩
    have hj' : j = j0 := Fin.ext hj
    subst hj'
    have hi : d₁ i ≤ ∑ k, d₁ k := Finset.single_le_sum (fun k _ => (h₁ k).le) (Finset.mem_univ i)
    have hpos : 0 < 1 + ∑ k, d₁ k := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := h₂ j0
    nlinarith

lemma isSiegel_glue {s m : ℕ} {e₁ : Fin s → ℝ} {u₁ : Matrix (Fin s) (Fin s) ℝ} {e₂ : Fin m → ℝ}
    {u₂ : Matrix (Fin m) (Fin m) ℝ} (h₁ : IsSiegel e₁ u₁) (h₂ : IsSiegel e₂ u₂)
    (hj : ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → e₁ i ≤ 4 * e₂ j) :
    IsSiegel (Fin.append e₁ e₂) (siegelGlueMat u₁ u₂) where
  nonneg i := by
    induction i using Fin.addCases with
    | left a => simpa using h₁.nonneg a
    | right a => simpa using h₂.nonneg a
  step p q h := by
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd] at h
        simpa using h₁.step a b h
      | right b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := a.isLt
        simpa using hj a b (by omega)
    | right a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := b.isLt
        omega
      | right b =>
        simp only [Fin.val_natAdd] at h
        simpa using h₂.step a b (by omega)
  diag i := by
    induction i using Fin.addCases with
    | left a => simpa using h₁.diag a
    | right a => simpa using h₂.diag a
  lower i j h := by
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.lower a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.lower a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)
  upper i j h := by
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.upper a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.upper a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)

lemma isSiegel_zero_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u) :
    IsSiegel (0 : Fin n → ℝ) u where
  nonneg _ := le_refl _
  step _ _ _ := by simp
  diag := h.diag
  lower := h.lower
  upper := h.upper

lemma isSiegel_smul_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u)
    {t : ℝ} (ht : 0 ≤ t) : IsSiegel (fun i => t * d i) u where
  nonneg i := mul_nonneg ht (h.nonneg i)
  step p q hpq := by
    have := h.step p q hpq
    nlinarith
  diag := h.diag
  lower := h.lower
  upper := h.upper

theorem siegelData_glue_scaled : ∀ (s m : ℕ) (d₁ : Fin s → ℝ) (u₁ : Matrix (Fin s) (Fin s) ℝ) (d₂ : Fin m → ℝ) (u₂ : Matrix (Fin m) (Fin m) ℝ), IsSiegel d₁ u₁ → IsSiegel d₂ u₂ → (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → ∃ (t : ℝ) (d d' : Fin (s + m) → ℝ) (u : Matrix (Fin (s + m)) (Fin (s + m)) ℝ), 0 < t ∧ IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j : Fin s, gram d u (Fin.castAdd m i) (Fin.castAdd m j) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.castAdd m j) = t * gram d₁ u₁ i j) ∧ (∀ (i : Fin s) (j : Fin m), gram d u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d u (Fin.natAdd s j) (Fin.castAdd m i) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d' u (Fin.natAdd s j) (Fin.castAdd m i) = 0) ∧ ∀ i j : Fin m, gram d u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j ∧ gram d' u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j := by
  intro s m d₁ u₁ d₂ u₂ h₁ h₂ p₁ p₂
  obtain ⟨t, ht, hj⟩ := siegelGlue_scale d₁ d₂ p₁ p₂
  refine ⟨t, Fin.append (0 : Fin s → ℝ) d₂, Fin.append (fun i => t * d₁ i) d₂, siegelGlueMat u₁ u₂, ht,
    isSiegel_glue (isSiegel_zero_of h₁) h₂ (fun i j _ => by simpa using (h₂.nonneg j)),
    isSiegel_glue (isSiegel_smul_of h₁ ht.le) h₂ hj, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using mul_pos ht (p₁ a)
    | right a => simpa using p₂ a
  · intro i j
    refine ⟨?_, ?_⟩
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue, Finset.mul_sum]
      simp only [siegelGlueMat_ll, siegelGlueMat_rl, Fin.append_left, Fin.append_right, zero_mul,
        mul_zero, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  · intro i j
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
  · intro i j
    refine ⟨?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue]
      simp

end GlobalTheory.RedTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformizationAbelian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem exists_pelUnif_torsionIso_subsingleton_of_abLocus {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (hR : IsCN R) (hpol : PolAt t (jK R))
    (hth : ThetaNZ t.G t.PP.L) (hab : ∀ x, x ∈ abLocus t.G) :
    ∃ P : PELUnif (maximalIdeal R) t, P.TorsionIso ∧ Subsingleton P.D.toPre.X := by
  obtain ⟨hn, hi, hc, hz⟩ := hR
  obtain ⟨l1, l2, l3, l4, l5, -⟩ := GlobalTheory.allSixLaws
  have hadm := GlobalTheory.isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hn hi hc
  have hpir : IsPrincipalIdealRing (R ⧸ maximalIdeal R) := by
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨P, hP⟩ := LN.UnifPrime.exists_pelUnif l1 l2 l3 l4 l5 LN.ega_holds uniformisation_dvr_unconditional
    LN.pelSt_holds E H R _ hadm hpir t hpol (GoodTrait.splitOver_of_abLocus t.G t.semi hab) hth
  refine ⟨P, hP, ?_⟩
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (CartesianMonoidalCategory.toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick R (maximalIdeal R) 0) p (hab _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GenFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (m g : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (ex : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ t.G)), IsOpen B → IsHolTo (B ×ˢ Set.univ) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) → (∀ b ∈ B, IsExpAt t (y b) (ex b)) → IsLatFam B (fun b => {w | ex b w = 1}) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | exact GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker <;> assumption)
end

