import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellStabiliserOfLocalRingBigCellLem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem exists_bigCell : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  intro H F E _ _ _ _ _ σ B d W r s hB hW v w hw g hg
  obtain ⟨hinj, -, -, -, -, -, -⟩ := GlobalTheory.T.inertCompletionToAdeles_properties σ hw
  obtain ⟨gmul, gone, ginj, gat, gsurj, gvec⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d ⊕ Fin d)
  obtain ⟨gmul', gone', -, -, -, gvec'⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d)
  obtain ⟨hJ, -, -⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d ⊕ Fin d)
  obtain ⟨-, hdiag, hhalfblk⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d)
  obtain ⟨b, δ, hb, hδ, hint, hdet, hdetinv⟩ := GlobalTheory.T.exists_unimodular_frame_inertPlace σ B W r s hB hW hw
  obtain ⟨cc, cO, h2, calg⟩ := GlobalTheory.T.inertCompletionConjugation_properties σ B hB hw
  have hlat := GlobalTheory.T.mem_adelicLatticeAtFinitePlace_iff_inert hw W

  have hvec : ∀ x : Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.InertSph.latAt W v ↔ InLat (w.adicCompletionIntegers E) b x := by
    intro x
    rw [hlat]
    constructor
    · rintro ⟨u, hu, he⟩
      have hxu : x = u := funext fun i => hinj (congrFun he i)
      subst hxu
      exact (hb x).1 hu
    · intro hx
      exact ⟨x, (hb x).2 hx, rfl⟩
  have hvec2 : ∀ x : Fin d ⊕ Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.DblVac.latD W v ↔ InLat2 (w.adicCompletionIntegers E) b x := by
    intro x
    exact and_congr (hvec (x ∘ Sum.inl)) (hvec (x ∘ Sum.inr))
  have hsurj2 : ∀ z ∈ GlobalTheory.DblVac.latD W v, ∃ x : Fin d ⊕ Fin d → w.adicCompletion E,
      z = fun i => iotaW hw (x i) := by
    rintro z ⟨h1, h2⟩
    obtain ⟨x1, -, e1⟩ := (hlat _).1 h1
    obtain ⟨x2, -, e2⟩ := (hlat _).1 h2
    refine ⟨Sum.elim x1 x2, funext fun i => ?_⟩
    rcases i with i | i
    · exact congrFun e1 i
    · exact congrFun e2 i

  have hpres : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x)) →
      ∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
    intro P hP z hz
    obtain ⟨x, rfl⟩ := hsurj2 z hz
    rw [gvec]
    exact (hvec2 _).2 (hP x ((hvec2 x).1 hz))
  have hpres' : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v) →
      ∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x) := by
    intro P hP x hx
    have := hP _ ((hvec2 x).2 hx)
    rw [gvec] at this
    exact (hvec2 _).1 this

  have e1 : incM F (dbl W.J) = dbl (incM F W.J) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]
  have e2 : (dbl W.J).map (algebraMap E (w.adicCompletion E)) = dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  have hskew : (W.J.map (algebraMap E (w.adicCompletion E)))ᵀ =
      -(W.J.map (algebraMap E (w.adicCompletion E))).map (conjW σ hw) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, calg, hW.skew j i, map_neg, neg_neg]
  have h2ne : (2 : w.adicCompletion E) ≠ 0 := by
    have h := (algebraMap E (w.adicCompletion E)).injective.ne (two_ne_zero : (2 : E) ≠ 0)
    rw [show (2 : w.adicCompletion E) = algebraMap E (w.adicCompletion E) 2 from (map_ofNat _ 2).symm]
    exact h

  obtain ⟨hgat, hglat⟩ := hg
  have hgg : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
  have hgg' : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := Units.inv_mul g.1
  have hginvat : At (evFin F v) (GlobalTheory.DblVac.matD g⁻¹ - 1) := by
    intro u hu
    have e : GlobalTheory.DblVac.matD g⁻¹ - 1 = -(GlobalTheory.DblVac.matD g⁻¹ * (GlobalTheory.DblVac.matD g - 1)) := by
      rw [Matrix.mul_sub, hgg', Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hgat u hu, Matrix.mul_zero, neg_zero]
  obtain ⟨P, hP⟩ := gsurj _ hgat
  obtain ⟨Q, hQ⟩ := gsurj _ hginvat
  have hPQ : P * Q = 1 := ginj (by rw [gmul, hP, hQ, gone]; exact hgg)
  have hU : Pᵀ * dbl (W.J.map (algebraMap E (w.adicCompletion E))) * P.map (conjW σ hw) =
      dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    rw [← e2]
    apply (hJ (dbl W.J) P).1
    rw [hP, e1]
    exact g.2
  have hPlat : ∀ z, InLat2 (w.adicCompletionIntegers E) b z →
      InLat2 (w.adicCompletionIntegers E) b (P *ᵥ z) ∧ InLat2 (w.adicCompletionIntegers E) b (Q *ᵥ z) :=
    fun z hz => ⟨hpres' P (fun y hy => by rw [hP]; exact (hglat y hy).1) z hz,
      hpres' Q (fun y hy => by rw [hQ]; exact (hglat y hy).2) z hz⟩

  obtain ⟨P0, P0', hPP, hP0U, hP0d, hP0lat, N, hN, hNlat⟩ :=
    GlobalTheory.T.inertPlace_bigCell_local_unitary_decomposition H (w.adicCompletionIntegers E) (conjW σ hw) cc cO h2 h2ne
      (W.J.map (algebraMap E (w.adicCompletion E))) hskew b δ hδ hint hdet hdetinv P Q hPQ hU hPlat

  let u : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨glueW hw P0, glueW hw P0', by rw [← gmul, hPP, gone], by
      have hPP' : P0' * P0 = 1 := mul_eq_one_comm.mp hPP
      rw [← gmul, hPP', gone]⟩
  have hu : u ∈ UG (cA σ) (dbl (incM F W.J)) := by
    show (glueW hw P0)ᵀ * dbl (incM F W.J) * (glueW hw P0).map (cA σ) = dbl (incM F W.J)
    rw [← e1]
    apply (hJ (dbl W.J) P0).2
    rw [e2]
    exact hP0U
  let p : GlobalTheory.DblVac.UD σ W := ⟨u, hu⟩
  have hp : GlobalTheory.DblVac.matD p = glueW hw P0 := rfl
  have hp' : GlobalTheory.DblVac.matD p⁻¹ = glueW hw P0' := rfl
  have hmul : ∀ a c : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * c) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD c :=
    fun _ _ => rfl
  have hpl : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0 (fun x hx => (hP0lat x hx).1)
  have hpl' : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p⁻¹ *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0' (fun x hx => (hP0lat x hx).2)
  have hpg : GlobalTheory.DblVac.matD (p * g) = glueW hw (P0 * P) := by
    rw [gmul, hP]
    rfl
  refine ⟨p, ⟨?_, fun z hz => ⟨hpl z hz, hpl' z hz⟩⟩, ⟨1, ?_⟩, ⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hp]
    exact gat P0
  · rw [hp]
    refine (hdiag P0 hP0d).trans ?_
    exact (Matrix.mul_one _).symm
  · rw [hpg]
    exact gat _
  · rw [hmul, ← Matrix.mulVec_mulVec]
    exact hpl _ (hglat z hz).1
  · rw [mul_inv_rev, hmul, ← Matrix.mulVec_mulVec]
    exact (hglat _ (hpl' z hz)).2
  ·
    refine ⟨glueW hw N, ?_, ?_⟩
    · have hd : GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = glueW hw ((2 : w.adicCompletion E)⁻¹ •
          ((P0 * P).toBlocks₁₁ + (P0 * P).toBlocks₁₂ + (P0 * P).toBlocks₂₁ + (P0 * P).toBlocks₂₂)) := by
        unfold GlobalTheory.DblVac.diagonalBlockOfMatrix
        rw [hpg]
        exact hhalfblk _
      rw [hd, ← gmul', hN, gone']
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (hlat z).1 hz
      rw [gvec']
      exact (hvec _).2 (hNlat x ((hb x).1 hx))

end GlobalTheory.InertBigCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelEmbeddingSecond
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.DetUnit

theorem isUnit_det_of_factor {R : Type} [CommRing R] {m g : ℕ} (h U : Fin m → Fin g → R)
    (M : Matrix (Fin m) (Fin m) R) (C : Fin m → Fin g → R) (hU : ∀ k b, U k b = ∑ j, M k j * C j b)
    (hP : IsUnit (pairDet h U)) : IsUnit M.det := by
  have e : (Matrix.of fun k k' : Fin m => ∑ b, h k' b * U k b) =
      M * Matrix.of (fun j k' => ∑ b, C j b * h k' b) := by
    ext k k'
    simp only [Matrix.of_apply, Matrix.mul_apply, hU, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  rw [pairDet, e, Matrix.det_mul] at hP
  exact isUnit_of_mul_isUnit_left hP

theorem det_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U h : Fin (Dw.mult σ) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → IsUnit (pairDet h U) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∀ (w : Fin (Dw.mult σ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (gm : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U i b)) (w i ≫ Y.m.φ)) → (letI := io.toAlgebra; ∀ i, IsCombAt y₀.1.x (y₀.1.u σ) (gm i) (w i ≫ ν.φ)) → ∃ u : T.Vˣ, algebraMap T.V T.Fr u = gm.det := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI σ A _ ξ β hξ g e U h he hU hP T α io y₀ yy hyy hpt w gm hw hgmC
  letI := io.toAlgebra
  have hyV : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ (spMap α ≫ ξ) := by rw [hyy, sp_sp]
  obtain ⟨v, hvt, hvb, hvg⟩ := GlobalTheory.T.integral_point_model_over_dvr E H Dw l l' Xo Xo' c c' W Y r ν σ T io y₀ (spMap α ≫ ξ) yy hyV hpt
  have he' := isTanBasis_bc he α
  have hchar := GlobalTheory.T.overInclusion_base_change_model E H Dw l l' Xo Xo' c c' W Y r hle hOI σ A ξ β hξ T.Fr ((algebraMap T.V T.Fr).comp α) io y₀.1 yy
    hyy hpt
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  choose u hut hu using fun k : Fin (Dw.mult σ) =>
    GlobalTheory.ShFam.Pad.Guard.exists_comb he'.1 (fun b => α (U k b))
  have hue : ∀ k (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) →
      u k ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u k := by
    intro k a z hz
    have hz' : z = α (β (embV c' W σ a)) := hinj (by rw [hz, ← hchar a]; rfl)
    subst hz'
    exact (hU T.V α) k (u k) (hu k) a
  choose M hM using fun k => hvb (u k) (hut k) (hue k)
  choose C hC using fun j => (he.2 T.V α (v j) (hvt j)).exists
  have hrel : ∀ k b, α (U k b) = ∑ j, M k j * C j b := by
    intro k b
    have h1 : IsCombAtG Y.t (spMap α ≫ ξ) (bcV Y.t α e) ((Matrix.of fun b j => C j b).mulVec (M k)) (u k) :=
      tanLinG (bcV Y.t α e) he'.1 v (Matrix.of fun b j => C j b) (M k) (u k) (fun j => hC j) (hM k)
    have h2 := congrFun ((he.2 T.V α (u k) (hut k)).unique (hu k) h1) b
    rw [h2]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hwu : ∀ k, w k ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u k := by
    intro k
    have h2 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) (hu k)
    have h3 := hw k
    rw [hyV] at h3
    have e1 : (fun j => spMap (dualMap (algebraMap T.V T.Fr)) ≫ bcV Y.t α e j) =
        bcV Y.t ((algebraMap T.V T.Fr).comp α) e := bcV_bcV (t := Y.t) α (algebraMap T.V T.Fr) e
    rw [e1] at h2
    exact GlobalTheory.FlatModel.LiftBC.isCombAtG_unique Y.t h3 h2
  have hgm : ∀ k, gm k = fun j => algebraMap T.V T.Fr (M k j) := by
    intro k
    have hte := GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI σ A ξ β hξ g (Dw.mult σ) e U he hU T.Fr
      ((algebraMap T.V T.Fr).comp α) io y₀.1 yy hyy hpt k (w k) (hw k)
    exact (y₀.1.basis σ (w k ≫ ν.φ) hte.1 hte.2).unique (hgmC k) (hvg (M k) (u k) (w k) (hM k) (hwu k))
  have hP' : IsUnit (pairDet (fun k b => α (h k b)) (fun k b => α (U k b))) := by
    have e2 : α (pairDet h U) = pairDet (fun k b => α (h k b)) (fun k b => α (U k b)) := by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext k k'
      simp [map_sum]
    exact e2 ▸ hP.map α
  have hMu : IsUnit (Matrix.of M).det :=
    isUnit_det_of_factor _ _ (Matrix.of M) C (fun k b => hrel k b) hP'
  refine ⟨hMu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  congr 1
  ext k j
  simp [hgm k]

end GlobalTheory.FlatModel.DetUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      (p : ℝ)⁻¹ ^ n < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∃ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) := by
  first | exact @GlobalTheory.FlatModel.exists_large_minors | exact GlobalTheory.FlatModel.exists_large_minors | (intros; apply GlobalTheory.FlatModel.exists_large_minors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicOverInclusion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem exists_denom (p : ℕ) [Fact p.Prime] : ∀ (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    (δ : ℂ_[p]) ≠ 0 ∧ ∀ l, (δ : ℂ_[p]) * d l ∈ 𝓞_ℂ_[p] := by
  intro m
  induction m with
  | zero => exact fun d => ⟨1, by simp, fun l => l.elim0⟩
  | succ m ih =>
    intro d
    obtain ⟨δ, hδ, hl⟩ := ih (Fin.tail d)
    by_cases ha : (δ : ℂ_[p]) * d 0 ∈ 𝓞_ℂ_[p]
    · refine ⟨δ, hδ, fun l => ?_⟩
      refine Fin.cases ha (fun l => ?_) l
      exact hl l
    · have hne : (δ : ℂ_[p]) * d 0 ≠ 0 := fun h => ha (h ▸ (𝓞_ℂ_[p]).zero_mem)
      have hinv : ((δ : ℂ_[p]) * d 0)⁻¹ ∈ 𝓞_ℂ_[p] := ((𝓞_ℂ_[p]).mem_or_inv_mem _).resolve_left ha
      refine ⟨δ * ⟨_, hinv⟩, ?_, fun l => ?_⟩
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ ≠ 0
        exact mul_ne_zero hδ (inv_ne_zero hne)
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l ∈ 𝓞_ℂ_[p]
        refine Fin.cases ?_ (fun l => ?_) l
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d 0 = 1 by
            rw [_root_.mul_comm (δ : ℂ_[p]), _root_.mul_assoc]; exact inv_mul_cancel₀ hne]
          exact (𝓞_ℂ_[p]).one_mem
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l.succ = ((δ : ℂ_[p]) * d 0)⁻¹ * ((δ : ℂ_[p]) * Fin.tail d l) by
            simp only [Fin.tail]; ring]
          exact (𝓞_ℂ_[p]).mul_mem _ _ hinv (hl l)

theorem exists_denom_alg : ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    algebraMap 𝓞_ℂ_[p] ℂ_[p] δ ≠ 0 ∧ ∀ l, ∃ e : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] e = algebraMap 𝓞_ℂ_[p] ℂ_[p] δ * d l := by
  intro p _ m d
  obtain ⟨δ, hδ, hl⟩ := exists_denom p m d
  exact ⟨δ, hδ, fun l => ⟨⟨_, hl l⟩, rfl⟩⟩

set_option maxHeartbeats 1000000 in

theorem htComb_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y →
    ∀ (z : FrPt Xo c ℂ_[p]) (gm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ_[p]) (am : ℂ_[p])
      (x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt), GlobalTheory.Frames.FrChg gm am z y →
      (∀ τ j, LieTie P (ψ ≫ ν.φ) (x τ j) (z.u τ j)) →
    ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
    ∀ (xb : Fin g → LieG P.Gt), (∀ b, ITie P π (xb b) (e b)) →
    ∀ (σ : E →+* ℂ) (U : Fin g → 𝓞_ℂ_[p]), (∀ u, IsCombAtG Y.t yb e U u → IsEigG Y.t (β.comp (embV c' W σ)) u) →
    ∃ (w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left) (cf : Fin (Dw.mult σ) → ℂ_[p]),
      IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) ∧
      IsCombAt y.x (y.u σ) cf (w ≫ ν.φ) ∧
      ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf j • ∑ l, gm σ j l • P.bLie (x σ l) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI p _ _ _ yb yy P π ψ y hHT z gm am x hchg hx β hβ g e _ xb hxb σ U hU
  obtain ⟨hPt, hTs, hptF, hHC⟩ := hHT
  obtain ⟨u0, hu0c, hu0t⟩ := GlobalTheory.T.exists_combination_lie_group_pullback E H Y.X Y.t p P yb π hPt.2.1 g e xb hxb U
  have hu0e := hU u0 hu0c
  obtain ⟨w, hw1, hw2, hw3, hwt⟩ := GlobalTheory.T.point_on_model_pullback_compatible E H Dw l' Xo' c' W Y p yb yy P π ψ hPt _ u0 hu0t
  have hbc := GlobalTheory.T.isCombAtG_base_change E H Y.X Y.t 𝓞_ℂ_[p] ℂ_[p] (algebraMap 𝓞_ℂ_[p] ℂ_[p]) yb g e U (β.comp (embV c' W σ)) u0
  have hA : IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) := by
    rw [hw1, ← hPt.1]
    exact hbc.1 hu0c
  have hemb := GlobalTheory.T.integral_model_p_adic_comparison E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p yb yy P π ψ y ⟨hPt, hTs, hptF, hHC⟩ β hβ σ
  have hE : ∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ := by
    intro a
    have h := hbc.2 hu0e a
    have hs : algebraMap 𝓞_ℂ_[p] ℂ_[p] (β (embV c' W σ a)) = algebraMap c.F ℂ_[p] (embK c σ a) := by
      rw [← algebraMap_embInt P.integers σ a, ← hemb]; rfl
    rw [hw1, h, RingHom.comp_apply, RingHom.comp_apply, hs]
  obtain ⟨hT, hEig⟩ := GlobalTheory.T.padic_point_model_abelian_map E H Dw l l' Xo Xo' c c' W Y r ν p yy y hptF w hw2 hw3 σ hE
  obtain ⟨cf, hcf, -⟩ := y.basis σ (w ≫ ν.φ) hT hEig
  refine ⟨w, cf, hA, hcf, ?_⟩
  have hyx : y.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hptF]
    exact (pullback.lift_fst _ _ _).symm
  have hzx : y.x = z.x := hchg.1
  have hψ' : IsGrpPullback P.A.A Xo.univ.t.G z.x (ψ ≫ ν.φ) := by
    rw [← hzx, hyx]
    exact hPt.2.2.2.1.comp ν.cart
  have hXt : LieTie P (ψ ≫ ν.φ) (lieComb P.Gt U xb) (w ≫ ν.φ) := by
    obtain ⟨xG, u', h1, h2, h3⟩ := hwt
    exact ⟨xG, u', h1, by rw [← h2, Category.assoc], h3⟩
  have hdc : IsCombAtG Xo.univ.t z.x (z.u σ) ((Matrix.of fun l j => gm σ j l).mulVec cf) (w ≫ ν.φ) :=
    tanLinG (z.u σ) (fun j => z.tan σ j) (y.u σ) (Matrix.of fun l j => gm σ j l) cf (w ≫ ν.φ)
      (fun j => hchg.2.1 σ j) (hzx ▸ hcf)
  obtain ⟨δ, hδ0, hδ⟩ := exists_denom_alg p _ ((Matrix.of fun l j => gm σ j l).mulVec cf)
  choose ee hee using hδ
  have hsc : IsCombAtG Xo.univ.t z.x (z.u σ) (fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] (ee l))
      (spMap (epsMul (algebraMap 𝓞_ℂ_[p] ℂ_[p] δ)) ≫ (w ≫ ν.φ)) := by
    have h := (isCombAtG_iff Xo.univ.t z.x (fun j => ovT (z.tan σ j)) _ (w ≫ ν.φ)).1 hdc
    refine (isCombAtG_iff Xo.univ.t z.x (fun j => ovT (z.tan σ j)) _ _).2 ?_
    rw [show (fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] (ee l)) =
      fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] δ * (Matrix.of fun l j => gm σ j l).mulVec cf l from funext hee,
      ← smT_combT, smT_left, h]
  have hL1 := hXt.scale δ
  have hL2 := GlobalTheory.T.isGrpPullback_tangent_combination E H Xo.X Xo.univ.t p P z.x (ψ ≫ ν.φ) hψ' _ (x σ) (z.u σ) ee _ (hx σ) hsc
  have heq := hL1.unique hψ'.1 hL2
  have hb := congrArg P.bLie heq
  rw [P.bLie_scale, bLie_lieComb, bLie_lieComb] at hb
  have hb' : algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ l, (Matrix.of fun l j => gm σ j l).mulVec cf l • P.bLie (x σ l) := by
    have e1 : algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = δ • ∑ b, U b • P.bLie (xb b) := by
      rw [algebraMap_smul]
      congr 1
    have e2 : ∑ l, ee l • P.bLie (x σ l) =
        algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ l, (Matrix.of fun l j => gm σ j l).mulVec cf l • P.bLie (x σ l) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, ← hee, algebraMap_smul]
    rw [e1, hb, e2]
  have h2 := smul_right_injective P.V hδ0 hb'
  rw [h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralModel_value_prod_zpow_localUnits : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (z : M.Z), (∀ w, y w ⤳ z) → ∀ {ι : Type} (s : Finset ι) (f : ι → Ω) (m : ι → ℤ), (∀ i, f i ≠ 0 ∧ f i ∈ M.O z ∧ (f i)⁻¹ ∈ M.O z) → M.val y (∏ i ∈ s, f i ^ m i) = ∏ i ∈ s, M.val y (f i) ^ m i := by
  first | exact @GlobalTheory.Poinc.RatModel.val_prod_zpow | exact GlobalTheory.Poinc.RatModel.val_prod_zpow | (intros; apply GlobalTheory.Poinc.RatModel.val_prod_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSection_expands_integrally_genericFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  first | exact @GlobalTheory.IntExpand.main | exact GlobalTheory.IntExpand.main | (intros; apply GlobalTheory.IntExpand.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_apply_constant_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ O r, dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.isInv_constFn | exact GlobalTheory.Heat.isInv_constFn | (intros; apply GlobalTheory.Heat.isInv_constFn <;> assumption)
end

