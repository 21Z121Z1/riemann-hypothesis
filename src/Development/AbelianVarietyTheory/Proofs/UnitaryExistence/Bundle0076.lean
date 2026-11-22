import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0009
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsInfEmb
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.RecModel

theorem exists_isInfEmb (D : D7) (τ : D.host.E →+* ℂ) :
    ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := by
  have := D.sp.cm.totReal
  set φ : D.host.F →+* ℂ := τ.comp (algebraMap D.host.F D.host.E) with hφ
  set w : InfinitePlace D.host.F := InfinitePlace.mk φ
  have hw : w.embedding = φ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)
  let _ : Algebra D.host.F ℂ := φ.toAlgebra
  let f : Ainf D.host.F →ₐ[D.host.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x => by
        show InfinitePlace.Completion.extensionEmbedding w (algebraMap D.host.F (Ainf D.host.F) x w) = φ x
        rw [InfiniteAdeleRing.algebraMap_apply, ← hw]
        exact InfinitePlace.Completion.extensionEmbedding_coe w _ }
  let g : D.host.E →ₐ[D.host.F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf D.host.F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[D.host.F] (1 : D.host.E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem exists_x0Orth {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    ∃ x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, ∀ Y : Data E r,
      (∀ τ, τ ∈ Y.Ψ → τ ∈ X.Ψ) → X.Gm = Y.Gm → X.p0 = Y.p0 → IsOrthogonalFrame Y x₀ := by
  classical
  refine ⟨fun τ => if h : τ ∈ X.Ψ then (X.signature ⟨τ, h⟩).choose else 1, fun Y hΨ hG hp τ hτ => ?_⟩
  rw [← hG, ← hp]
  have hτ' := hΨ τ hτ
  simp only [dif_pos hτ']
  exact (X.signature ⟨τ, hτ'⟩).choose_spec.2

theorem exists_recOK : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∃ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ ∧ GlobalTheory.FrameUnif.NegXi M ∧ ∀ io' : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io' → (∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io' x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io' y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm))) → RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io' th x₀ := by
  intro hH D Q hQ j hj σ' g ty F _ _
  have hr := D.sp.W_rank j hj.1 hj.2
  obtain ⟨io, hemb, -, hcc, hdet, hspan, hform⟩ := exists_latEmb_sign_one D Q hQ j hj
  let c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E) :=
    LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)
  let ψ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
    (c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ io
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
    have : Set.range ψ = c.toLinearMap '' Set.range io := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  obtain ⟨M, hB, hN, hM⟩ := GlobalTheory.ModelsExist.exists_modelsOf hH D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) σ' g ty F D.R.r
    (-D.host.xi0) (gmW (D.sp.W j) hr) ψ hξ (level_good_and_sign D Q hQ).2.2
    ⟨c.injective.comp hemb.1, hsp, hcc, hdet, hform⟩
  choose θ hθ using exists_isInfEmb D
  obtain ⟨x₀, hx₀⟩ := exists_x0Orth (M.X ⟨0, F.n_pos⟩)
  have hx : ∀ k, IsOrthogonalFrame (M.X k) x₀ := fun k =>
    hx₀ _ (fun τ hτ => ((hB.type _).2 τ).2 (((hB.type k).2 τ).1 hτ)) ((hM _).1.trans (hM k).1.symm)
      ((hB.type _).1.trans (hB.type k).1.symm)
  exact ⟨M, io, fun _ τ => θ τ.1, x₀, ⟨hB, hM, hemb, hform, fun _ τ => hθ τ.1, hx⟩, hN,
    fun io' h1 h2 => ⟨hB, hM, h1, h2, fun _ τ => hθ τ.1, hx⟩⟩

end GlobalTheory.RecModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNearOne
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_root_near_one : ∀ (D : D7), ∀ W ∈ 𝓝 (1 : (AE D)ˣ), ∃ N ∈ 𝓝 (1 : (AE D)ˣ), ∀ u ∈ N, (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (u : AE D) = 1 → ∃ x ∈ W, (x : AE D) = (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by
  intro D
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  exact GlobalTheory.AdLat.RootNear.exists_root_near D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
section
namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unit_form_inv {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    ∑ a, ∑ b, (g *ᵥ x) a * J b a * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * J b a * σ (y b) := by
  have key : ∀ (u v : Fin n → A), ∑ a, ∑ b, u a * J b a * σ (v b) = (σ ∘ v) ⬝ᵥ (J *ᵥ u) := by
    intro u v
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : σ ∘ (g *ᵥ y) = (σ ∘ y) ᵥ* Formalism.UG.cT σ g := by
    funext b
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [key, key, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem unit_det_norm {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hJ : IsUnit J.det) (h : Formalism.UG.cT σ g * J * g = J) : g.det * σ g.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (σ.map_det g).symm
  rw [h2] at h1
  apply hJ.mul_left_cancel
  linear_combination h1

theorem unitary_map {F E R S : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (h : Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J) :
    Formalism.UG.cT (sigR S σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom) * JR S J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = JR S J := by
  set π : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hπ
  have hs : ∀ z, π (sigR R σ z) = sigR S σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hπ, sigR]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hJ : (JR R J).map π = JR S J := by
    ext i j
    simp [hπ, JR, inclR]
  have hc : (Formalism.UG.cT (sigR R σ) g).map π = Formalism.UG.cT (sigR S σ) (g.map π) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hs]
  have h2 := congrArg (fun M => Matrix.map M π) h
  simp only [Matrix.map_mul] at h2
  rw [hJ, hc] at h2
  exact h2

theorem finHom_unitary {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (finHom V g).1 * JR (F := D.host.F) (Af D.host.F) V.gram * (finHom V g).1 =
      JR (F := D.host.F) (Af D.host.F) V.gram :=
  unitary_map (sndA D.host.F) D.sp.cm.sig V.gram (matHom V g).1
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finHom_herm_det : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  intro D V g
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R], IsUnit (JR (F := D.host.F) R V.gram).det := by
    intro R _ _
    have e : (JR (F := D.host.F) R V.gram).det = inclR (F := D.host.F) R V.gram.det := ((inclR (F := D.host.F) R).map_det V.gram).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne V)).map _
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · exact unit_form_inv _ _ _ (finHom_unitary V g) x y
  · exact unit_det_norm _ _ _ (hu _) (finHom_unitary V g)
  · exact unit_det_norm _ _ _ (hu _) (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalfOfPrimesIffLevelPb
section
noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_Mb (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.levelAt D l.Mb (isHalf_of_level D l hl) = l := by
  obtain ⟨M, h3, hodd, Mb, hK, hp, hc, A, hA⟩ := l
  obtain ⟨h1, h2⟩ := hl
  dsimp only at h1 h2
  subst h1 h2
  rfl

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

def levelEquivHalf (D : D7) :
    {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1} ≃
      {Mb : Ideal (𝓞 D.host.E) // HalfLevelCoefficients.IsHalf D Mb} where
  toFun l := ⟨l.1.Mb, isHalf_of_level D l.1 l.2⟩
  invFun Mb := ⟨HalfLevelCoefficients.levelAt D Mb.1 Mb.2, levelAt_spec D Mb.1 Mb.2⟩
  left_inv l := Subtype.ext (levelAt_Mb D l.1 l.2)
  right_inv _ := rfl

theorem datAt_eq (D : D7) : HalfLevelCoefficients.datAt D = datumAtLift D _ (datHolds D) := rfl

theorem parAt_levelAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E))
    (h : HalfLevelCoefficients.IsHalf D Mb) :
    Formalism.L2.Pj.parAt D hF hz hN (HalfLevelCoefficients.levelAt D Mb h) (levelAt_spec D Mb h) = HalfLevelCoefficients.parAt D hF hz hN Mb h :=
  rfl

theorem parAt_eq (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    Formalism.L2.Pj.parAt D hF hz hN l hl = HalfLevelCoefficients.parAt D hF hz hN l.Mb (isHalf_of_level D l hl) := by
  rw [← parAt_levelAt]
  congr 1
  exact (levelAt_Mb D l hl).symm

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

theorem halfOfPrimes_iff_levelPb (D : D7) :
    HalfLevelCoefficients.HalfOfPrimes D ↔ ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K),
      (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → LevelPb D pb :=
  forall₂_congr fun pb _ => (levelPb_iff D pb).symm

theorem typings_agree (D : D7) :
    (∀ l : {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1}, (levelEquivHalf D l).1 = l.1.Mb) ∧
    (∀ (hF : OFull D) (hz : OZeta D) (hN : N1ab)
      (l : {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1}),
      Formalism.L2.Pj.parAt D hF hz hN l.1 l.2 =
        HalfLevelCoefficients.parAt D hF hz hN (levelEquivHalf D l).1 (levelEquivHalf D l).2) ∧
    (∀ (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : {Mb : Ideal (𝓞 D.host.E) // HalfLevelCoefficients.IsHalf D Mb}),
      Formalism.L2.Pj.parAt D hF hz hN ((levelEquivHalf D).symm Mb).1 ((levelEquivHalf D).symm Mb).2 =
        HalfLevelCoefficients.parAt D hF hz hN Mb.1 Mb.2) ∧
    (∀ pb, LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb)) ∧
    (HalfLevelCoefficients.HalfOfPrimes D ↔ ∀ pb, HalfLevelCoefficients.PrimesOver D pb → LevelPb D pb) :=
  ⟨fun _ => rfl, fun hF hz hN l => parAt_eq D hF hz hN l.1 l.2,
    fun hF hz hN Mb => parAt_levelAt D hF hz hN Mb.1 Mb.2, levelPb_iff D, halfOfPrimes_iff_levelPb D⟩

end GlobalTheory.ParAtCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.L2FiniteVolumePackageLaws
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem norm_embedding_xi_zero (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem finVol_and_cuspL2_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, VolTieG D → V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hT hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  have hV : FinVol V := finVol_of_volTie hT V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV (volPair_of_tie hT V hs) P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans (by rw [map_neg, norm_neg]; exact norm_embedding_xi_zero D τ)

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProduct
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.LevelHalf

theorem map_comap_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) :
    (l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb := by
  refine le_antisymm Ideal.map_comap_le ?_
  have hw : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (LPb.w0K D) = H.w0 := by
    apply RingOfIntegers.ext
    have h2 : ((2 * H.w0 : 𝓞 D.host.E) : D.host.E) = ((1 + H.rt : 𝓞 D.host.E) : D.host.E) := by
      rw [H.two_weight_eq_one_add_root]
    have h3 : (2 : D.host.E) * (H.w0 : D.host.E) = 1 + (H.rt : D.host.E) := h2
    show ((1 + D.host.sqrtMinusD) / 2 : D.host.E) = (H.w0 : D.host.E)
    rw [← hrt, ← h3]
    field_simp
  conv_lhs => rw [l.fromK]
  rw [Ideal.span_le]
  rintro a ⟨ha, ha'⟩
  have hr : a ∈ (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)).toIntAlgHom.range := by
    refine Algebra.adjoin_le ?_ ha'
    rintro _ rfl
    exact ⟨LPb.w0K D, hw⟩
  obtain ⟨b, rfl⟩ := hr
  exact Ideal.mem_map_of_mem _ ha

theorem exists_prime_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {p : ℕ} (hp : p.Prime) (hpM : p ∣ l.M) :
    ∃ pb : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ pb.asIdeal ∧
      pb.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
  set I : Ideal (𝓞 D.host.K) := l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ⊔
    Ideal.span {(p : 𝓞 D.host.K)} with hI
  have hmap : I.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [hI, Ideal.map_sup, map_comap_half D H l hrt, Ideal.map_span, Set.image_singleton, map_natCast]
  have hbar : (Ideal.span {(p : 𝓞 D.host.E)}).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hnt := LPb.span_p_ne_top D hp
  have hle : Ideal.span {(p : 𝓞 D.host.K)} ≤ I := le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := congrArg Ideal.absNorm hJ
  rw [map_mul, LPb.absNorm_span_p] at hN
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN.symm)
  have hi1 : i = 1 := by
    interval_cases i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hieq
      rw [hieq, Ideal.map_top] at hmap
      have hmap' := congrArg (Ideal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) hmap
      rw [Ideal.map_top, Ideal.map_sup, hbar] at hmap'
      have hc := (Ideal.isCoprime_iff_sup_eq.2 hmap.symm).mul_left (Ideal.isCoprime_iff_sup_eq.2 hmap'.symm)
      rw [l.prod, Ideal.isCoprime_iff_sup_eq, sup_eq_right.2
        (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hpM))] at hc
      exact hnt hc
    · rfl
    · exfalso
      rw [hieq] at hN
      have hJ1 : Ideal.absNorm J = 1 :=
        Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN.symm.trans (mul_one _).symm)
      rw [Ideal.absNorm_eq_one_iff] at hJ1
      rw [hJ1, Ideal.mul_top] at hJ
      rw [← hJ, Ideal.map_span, Set.image_singleton, map_natCast] at hmap
      have h1 : l.Mb ≤ Ideal.span {(p : 𝓞 D.host.E)} := hmap ▸ le_sup_left
      have h2 : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {(p : 𝓞 D.host.E)} :=
        hbar ▸ Ideal.map_mono h1
      exact hnt (top_le_iff.1 (l.coprime ▸ sup_le h1 h2))
  rw [hi1, pow_one] at hieq
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hieq
    exact hp.ne_zero hieq.symm
  exact ⟨⟨I, hprime, hne⟩, hle (Ideal.subset_span rfl), hmap⟩

theorem eq_mul_sup {R : Type*} [CommRing R] (I : Ideal R) {a b : R} (hab : IsCoprime a b) (h : a * b ∈ I) :
    I = (I ⊔ Ideal.span {a}) * (I ⊔ Ideal.span {b}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, v, huv⟩ := hab
    have e : x = (u * a) * x + x * (v * b) := by linear_combination (-x) * huv
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
        (Ideal.mem_sup_left hx))
      (Ideal.mul_mem_mul (Ideal.mem_sup_left hx)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))))
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))

theorem good_and_half_eq_prod : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), (H.rt : D.host.E) = D.host.sqrtMinusD → l.M = D.host.g 0 * D.host.g 1 → (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  intro D H l hrt hM
  refine ⟨fun p _ => GlobalTheory.PinNum.goodAt_of_two_primes l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, ?_⟩
  have hd : ∀ k : Fin 2, D.host.g k ∣ l.M := by
    intro k
    rw [hM]
    fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  choose pb h1 h2 using fun k => exists_prime_half D H l hrt (D.host.g_prime k) (hd k)
  refine ⟨pb, h1, ?_⟩
  rw [Fin.prod_univ_two, h2 0, h2 1]
  apply eq_mul_sup
  · exact Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  · rw [← Nat.cast_mul, ← hM]
    have : Ideal.span {((l.M : ℕ) : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)

end GlobalTheory.LevelHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem infiniteAdele_bijective : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  intro D
  have hτ : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ (cF D x) = starRingEnd ℂ (τ x) :=
    fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : cF D ≠ 1 := by
    intro h
    have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
    have h1 := hτ D.host.φ₀ D.host.sqrtMinusD
    rw [h, AlgEquiv.one_apply] at h1
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    exact h0.2.2 (by linarith)
  have H := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E (cF D) D.sp.cm.deg2 hc D.sp.cm.totReal hτ
  refine ⟨?_, fun θ hθ => ?_⟩
  · choose θ hθ using H.1
    exact ⟨θ, hθ⟩
  · obtain ⟨h1, h2, h3⟩ := H.2 θ hθ
    refine ⟨h1, h2, h3 {τ | τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} fun τ => ?_⟩
    have := cm_type_mem_iff_conj_not_mem D τ
    rw [mem_cm_type_iff, mem_cm_type_iff] at this
    exact this

end GlobalTheory.Member
end
end

